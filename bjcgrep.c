/*
* Copyright © 2018 Benjamin Cooke <bcooke@freedomofknowledge.org>
* This work is free. You can redistribute it and/or modify it under the
* terms of the Do What The Fuck You Want To Public License, Version 2,
* as published by Sam Hocevar. See the COPYING file for more details.
*/

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <arpa/inet.h>
#include <sys/mman.h>

#ifdef DEBUG
#define DEBUG_REGEX_FILENAME "./regex.obj"
static FILE *dbg_file = NULL;
#endif

#define REGEX_EXEC_CAP 4194304
#define STACK_CAP 256
#define UNION_HEADER_SIZE 4096
#define NOP_PAD_SIZE 18
#define INPUT_INIT_CAP (4096-32)

#define MEM_PROT_FLAGS (PROT_READ|PROT_WRITE|PROT_EXEC)
#define MEM_MAP_FLAGS (MAP_ANONYMOUS|MAP_PRIVATE)

/* Indicates a meta-character */
#define META 0xFF00

/* High bit allows for distinction between NonTerminal and state */
typedef enum NonTerminal {
	R = (signed int) 0x8000FF00,
	T = (signed int) 0x8000FF01
} NonTerminal_t;

typedef union {
	NonTerminal_t nt;
	uint16_t ch;
	int32_t state;
} item_t;

typedef int32_t (*regex_func_t)(const char *s);

static item_t            _pstack[STACK_CAP];
static item_t*           pstack = _pstack;
static uint8_t*          regex_exec_mem = NULL;
static uint8_t*          regex_exec_tail = NULL;
static regex_func_t      _transition_stack[STACK_CAP];
static regex_func_t*     transition_stack = _transition_stack - 1;
static regex_func_t      _edge_stack[STACK_CAP];
static regex_func_t*     edge_stack = _edge_stack - 1;
static int32_t           match = 0;


/* Non-Reentrant */
static uint16_t lex( const char *s ) {
	static int i = 0;

	if ( s[i] == '\\' ) {
		i++;
		if ( s[i] == '*' ||s[i] == '|' || s[i] == '(' || s[i] == ')' || s[i] == '\\' ) {
			return s[i++];
		}
		else {
			return '\\';
		}
	}
	else {
		if ( s[i] == '*' || s[i] == '|' || s[i] == '(' || s[i] == ')' ) {
			return META | s[i++];
		}
		else {
			return s[i++];
		}
	}
}


static void transition_push( void *noarg, regex_func_t f ) {
	noarg = noarg;
	*(++edge_stack) = f;
}


static int transition_flush( const char *c ) {

	while ( transition_stack != _transition_stack - 1 && match == 0 ) {
		match = (*transition_stack)(c);
		transition_stack--;
	}

	for ( ; edge_stack != _edge_stack - 1; edge_stack-- ) {
		*(++transition_stack) = *edge_stack;
	}

	if ( match != 0 || *c == '\0' ) {
		for ( ; transition_stack != _transition_stack - 1; transition_stack-- );
		return 1;
	}

	return 0;
}


static void accept_edge( void ) {

	/* movl $1, %eax */
	*(regex_exec_tail++) = 0xB8;
	*((uint32_t *) regex_exec_tail) = 1;
	regex_exec_tail += 4;

	/* ret */
	*(regex_exec_tail++) = 0xC3;

}


static uint64_t* accept_jmp( void ) {

	regex_func_t *accept_addr;

	/* movq [accept_addr], %r8 */
	*((uint16_t *) regex_exec_tail) = htons( 0x49B8 );
	regex_exec_tail += 2;
	accept_addr = (regex_func_t *) regex_exec_tail;
	regex_exec_tail += 8;

	/* jmp *$r8 */
	*(regex_exec_tail++) = 0x41;
	*(regex_exec_tail++) = 0xFF;
	*(regex_exec_tail++) = 0xE0;

	return (uint64_t *) accept_addr;

}


static uint64_t* union_edge( uint8_t *union_header, unsigned int *offset ) {

	regex_func_t *edge_addr;

	/* movq [edge_addr], %r8 */
	*((uint16_t *) (union_header + *offset)) = htons( 0x49B8 );
	*offset += 2;
	edge_addr = (regex_func_t *) (union_header + *offset);
	*offset += 8;

	/* call *%r8 */
	*(union_header + (*offset)++) = 0x41;
	*(union_header + (*offset)++) = 0xFF;
	*(union_header + (*offset)++) = 0xD0;

	/* andl %eax, %eax */
	*((uint16_t *) (union_header + *offset)) = htons( 0x21C0 );
	*offset += 2;

	/* jz +1 */
	*((uint16_t *) (union_header + *offset)) = htons( 0x7401 );
	*offset += 2;

	/* ret */
	*(union_header + (*offset)++) = 0xC3;

	return (uint64_t *) edge_addr;

}


static uint64_t* null_edge( void ) {

	regex_func_t *edge_addr;

	/* movq [edge_addr], %r8 */
	*((uint16_t *) regex_exec_tail) = htons( 0x49B8 );
	regex_exec_tail += 2;
	edge_addr = (regex_func_t *) regex_exec_tail;
	regex_exec_tail += 8;

	/* call *%r8 */
	*(regex_exec_tail++) = 0x41;
	*(regex_exec_tail++) = 0xFF;
	*(regex_exec_tail++) = 0xD0;

	/* andl %eax, %eax */
	*((uint16_t *) regex_exec_tail) = htons( 0x21C0 );
	regex_exec_tail += 2;

	/* jz +1 */
	*((uint16_t *) regex_exec_tail) = htons( 0x7401 );
	regex_exec_tail += 2;

	/* ret */
	*(regex_exec_tail++) = 0xC3;

	return (uint64_t *) edge_addr;

}


static uint64_t* transit_edge( void ) {

	regex_func_t *edge_addr;

	/* movq [edge_addr], %rsi */
	*((uint16_t *) regex_exec_tail) = htons( 0x48BE );
	regex_exec_tail += 2;
	edge_addr = (regex_func_t *) regex_exec_tail;
	regex_exec_tail += 8;

	/* movq [transition_push], %r8 */
	*((uint16_t *) regex_exec_tail) = htons( 0x49B8 );
	regex_exec_tail += 2;
	*((uint64_t *) regex_exec_tail) = (uint64_t) transition_push;
	regex_exec_tail += 8;

	/* call *%r8 */
	*(regex_exec_tail++) = 0x41;
	*(regex_exec_tail++) = 0xFF;
	*(regex_exec_tail++) = 0xD0;

	return (uint64_t *) edge_addr;

}


static uint64_t* concat( char c ) {

	/* movq [c], %rcx */
	*(regex_exec_tail++) = 0x48;
	*(regex_exec_tail++) = 0xC7;
	*(regex_exec_tail++) = 0xC1;
	*((uint32_t *) regex_exec_tail) = c;
	regex_exec_tail += 4;

	/* movb (%rdi), %dl */
	*((uint16_t *) regex_exec_tail) = htons( 0x8A17 );
	regex_exec_tail += 2;

	/* andq $0xFF, %rdx */
	*(regex_exec_tail++) = 0x48;
	*(regex_exec_tail++) = 0x81;
	*(regex_exec_tail++) = 0xE2;
	*((uint32_t *) regex_exec_tail) = 0xFF;
	regex_exec_tail += 4;

	/* subq %rdx, %rcx */
	*(regex_exec_tail++) = 0x48;
	*(regex_exec_tail++) = 0x29;
	*(regex_exec_tail++) = 0xD1;

	/* jrcxz +1 */
	*((uint16_t *) regex_exec_tail) = htons( 0xE303 );
	regex_exec_tail += 2;

	/* xorl %eax, %eax */
	*((uint16_t *) regex_exec_tail) = htons( 0x31C0 );
	regex_exec_tail += 2;

	/* ret */
	*(regex_exec_tail++) = 0xC3;

	return transit_edge();

}


static char* fetchline( FILE* stream  ) {

	static size_t capacity = INPUT_INIT_CAP;
	char *line, *tmp;
	int c, i;


	if ( (line = (char *) malloc( sizeof(char) * capacity )) == NULL ) {
		return NULL;
	}


	for ( i = 0; (c = fgetc( stream )) != EOF && c != '\n'; i++ ) {

		line[i] = c;

		if ( i == (capacity - 1) ) {
			capacity += 32;
			capacity *= capacity;
			capacity -= 32;

			if ( (tmp = (char *) malloc( sizeof(char) * capacity )) == NULL ) {
				free( line );
				return NULL;
			}

			memcpy( tmp, line, sizeof(char) * (i + 1) );

			free( line );
			line = tmp;
			tmp = NULL;
		}

	}

	line[i] = '\0';

	if ( c == EOF ) {
		free(line);
		line = NULL;
	}

	return line;

}


int main( int argc, char** argv ) {

	int32_t state;
	uint16_t c;
	bool shift, accept;
	char *input, *it;
	int retval = 1;

	uint64_t last_concat;
	unsigned int null_offset;
	uint64_t *forward_addr, *backward_addr, *edge_addr;
	uint64_t *subexpr_head_stack, *union_head_stack;
	uint64_t **accept_addr_stack;
	unsigned int *union_offset_stack;
	static uint64_t _subexpr_head_stack[STACK_CAP];
	static uint64_t _union_head_stack[STACK_CAP];
	static uint64_t *_accept_addr_stack[STACK_CAP];
	static unsigned int _union_offset_stack[STACK_CAP];

	subexpr_head_stack = _subexpr_head_stack;
	union_head_stack = _union_head_stack;
	accept_addr_stack = _accept_addr_stack;
	union_offset_stack = _union_offset_stack;

	if ( argc != 2 ) {
		fprintf( stderr, "Usage: %s [regex]\n", argv[0] );
		return 1;
	}

	shift = true;
	accept = false;
	pstack->state = (state = 0);
	regex_exec_mem = mmap( NULL, REGEX_EXEC_CAP, MEM_PROT_FLAGS, MEM_MAP_FLAGS, -1, 0 );
	*union_head_stack = (uint64_t) (regex_exec_tail = regex_exec_mem);
	*subexpr_head_stack = (uint64_t) (regex_exec_tail += UNION_HEADER_SIZE);
	*union_offset_stack = 0;
	*accept_addr_stack = NULL;

	while ( state >= 0 && !accept ) {

		if ( shift ) {
			c = lex( argv[1] );
		}

		switch ( state ) {

			/* Shift states are merged to avoid redundant code in exchange
			 * for more conditionals */
			case 0:
			case 1:
			case 2:
			case 3:
			case 4:
				if ( !(META & c) && c != 0 ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 5);
				}
				else if ( c == (META | '(') ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 2);

					*(++union_head_stack) = (uint64_t) regex_exec_tail;
					*(++union_offset_stack) = NOP_PAD_SIZE;
					memset( (uint8_t *) *union_head_stack, 0x90, NOP_PAD_SIZE );
					*(++subexpr_head_stack) = (uint64_t) (regex_exec_tail += UNION_HEADER_SIZE);
					*(++accept_addr_stack) = NULL;
				}
				else if ( state == 3 && c == (META | ')') ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 6);
				}
				else if ( (state == 1 || state == 3) && c == (META | '|') ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 4);

					edge_addr = union_edge( (uint8_t *) *union_head_stack, union_offset_stack );

					*(++accept_addr_stack) = accept_jmp();

					*edge_addr = (uint64_t) regex_exec_tail;
				}
				else if ( (state == 0 || state == 1) && c == 0 ) {
					accept = true;

					edge_addr = union_edge( (uint8_t *) *union_head_stack, union_offset_stack );
					*((uint8_t *) (*(union_head_stack--) + *(union_offset_stack--))) = 0xC3;
					*edge_addr = *(subexpr_head_stack--);

					for (; *accept_addr_stack != NULL; accept_addr_stack--) {
						**accept_addr_stack = (uint64_t) regex_exec_tail;
					}
					accept_addr_stack--;

					accept_edge();
				}
				else {
					/* Give one's complement of state in case of error */
					state ^= -1;
				}
				break;


			case 5:
				shift = false;
				if ( c == (META | '*') ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 7);
					break;
				}
				if ( (META & (--pstack)->ch) || pstack->ch == 0 ) {
					state ^= -1;
					break;
				}

				last_concat = (uint64_t) regex_exec_tail;
				edge_addr = concat( pstack->ch );

				/* xorl %eax, %eax */
				*((uint16_t *) regex_exec_tail) = htons( 0x31C0 );
				regex_exec_tail += 2;

				/* ret */
				*(regex_exec_tail++) = 0xC3;

				*edge_addr = (uint64_t) regex_exec_tail;

				--pstack;
	
				if ( pstack->state == 0 || pstack->state == 2 ) {
					state = 11;
				}
				else if ( pstack->state == 1 || pstack->state == 3 ) {
					state = 10;
				}
				else if ( pstack->state == 4 ) {
					state = 9;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = T;
				(++pstack)->state = state;
				break;


			case 6:
				shift = false;
				if ( c == (META | '*') ) {
					shift = true;
					(++pstack)->ch = c;
					(++pstack)->state = (state = 8);
					break;
				}
				if ( (--pstack)->ch != (META | ')') ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->nt != R ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->ch != (META | '(') ) {
					state ^= -1;
					break;
				}
				--pstack;

				last_concat = *(union_head_stack--);
				edge_addr = union_edge( (uint8_t *) last_concat, union_offset_stack );
				*((uint8_t *) (last_concat + *(union_offset_stack--))) = 0xC3;

				*edge_addr = *(subexpr_head_stack--);

				for (; *accept_addr_stack != NULL; accept_addr_stack--) {
					**accept_addr_stack = (uint64_t) regex_exec_tail;
				}
				accept_addr_stack--;

				if ( pstack->state == 0 || pstack->state == 2 ) {
					state = 11;
				}
				else if ( pstack->state == 1 || pstack->state == 3 ) {
					state = 10;
				}
				else if ( pstack->state == 4 ) {
					state = 9;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = T;
				(++pstack)->state = state;
				break;


			case 7:
				shift = false;
				if ( (--pstack)->ch != (META | '*') ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (META & (--pstack)->ch) || pstack->ch == 0 ) {
					state ^= -1;
					break;
				}

				forward_addr = null_edge();
				last_concat = (uint64_t) regex_exec_tail;
				edge_addr = concat( pstack->ch );
				backward_addr = transit_edge();

				/* xorl %eax, %eax */
				*((uint16_t *) regex_exec_tail) = htons( 0x31C0 );
				regex_exec_tail += 2;

				/* ret */
				*(regex_exec_tail++) = 0xC3;

				*forward_addr = (uint64_t) regex_exec_tail;
				*edge_addr = (uint64_t) regex_exec_tail;
				*backward_addr = (uint64_t) last_concat;

				--pstack;

				if ( pstack->state == 0 || pstack->state == 2 ) {
					state = 11;
				}
				else if ( pstack->state == 1 || pstack->state == 3 ) {
					state = 10;
				}
				else if ( pstack->state == 4 ) {
					state = 9;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = T;
				(++pstack)->state = state;
				break;


			case 8:
				shift = false;
				if ( (--pstack)->ch != (META | '*') ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->ch != (META | ')') ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->nt != R ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->ch != (META | '(') ) {
					state ^= -1;
					break;
				}
				--pstack;

				last_concat = *(union_head_stack--);
				null_offset = 0;

				/* overwrite nop padding to add null forward edge */
				forward_addr = union_edge((uint8_t *) last_concat, &null_offset);

				edge_addr = union_edge( (uint8_t *) last_concat, union_offset_stack );
				*((uint8_t *) (last_concat + *(union_offset_stack--))) = 0xC3;

				for (; *accept_addr_stack != NULL; accept_addr_stack--) {
					**accept_addr_stack = (uint64_t) regex_exec_tail;
				}
				accept_addr_stack--;

				backward_addr = null_edge();

				*forward_addr = (uint64_t) regex_exec_tail;
				*edge_addr = *(subexpr_head_stack--);
				*backward_addr = last_concat + null_offset;

				if ( pstack->state == 0 || pstack->state == 2 ) {
					state = 11;
				}
				else if ( pstack->state == 1 || pstack->state == 3 ) {
					state = 10;
				}
				else if ( pstack->state == 4 ) {
					state = 9;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = T;
				(++pstack)->state = state;
				break;


			case 9:
				if ( (--pstack)->nt != T ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->ch != (META | '|') ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->nt != R ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( pstack->state == 0 ) {
					state = 1;
				}
				else if ( pstack->state == 2 ) {
					state = 3;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = R;
				(++pstack)->state = state;
				break;


			case 10:
				if ( (--pstack)->nt != T ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( (--pstack)->nt != R ) {
					state ^= -1;
				}
				--pstack;
				if ( pstack->state == 0 ) {
					state = 1;
				}
				else if ( pstack->state == 2 ) {
					state = 3;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = R;
				(++pstack)->state = state;
				break;


			case 11:
				if ( (--pstack)->nt != T ) {
					state ^= -1;
					break;
				}
				--pstack;
				if ( pstack->state == 0 ) {
					state = 1;
				}
				else if ( pstack->state == 2 ) {
					state = 3;
				}
				else {
					state ^= -1;
					break;
				}
				(++pstack)->nt = R;
				(++pstack)->state = state;
				break;


			default:
				state ^= -1;
				break;

		}
	}

	if ( accept == false ) {
		fprintf( stderr, "Parse error in state %d.\n", (state ^ -1) );
		munmap(regex_exec_mem, REGEX_EXEC_CAP);
		return 1;
	}


#ifdef DEBUG
	if ((dbg_file = fopen( DEBUG_REGEX_FILENAME, "w" )) == NULL) {
		perror("Could not dump regex to file");
		munmap(regex_exec_mem, REGEX_EXEC_CAP);
		return 1;
	}

	fwrite( regex_exec_mem, 1, REGEX_EXEC_CAP, dbg_file );
	fprintf( stderr, "DEBUG: &regex = %lx\n", (uint64_t) regex_exec_mem );
	fclose(dbg_file);
	dbg_file = NULL;
#endif


	while ( (input = fetchline( stdin )) != NULL) {
		it = input;

		do {
			*(++transition_stack) = regex_exec_mem;
		} while ( transition_flush( it++ ) != 1 );

		if ( match != 0 ) {
			printf("%s\n", input);
			fflush(stdout);
			retval = 0;
			match = 0;
		}

		free(input);
		input = NULL;
	}

	munmap(regex_exec_mem, REGEX_EXEC_CAP);

	return retval;

}
