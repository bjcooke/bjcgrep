CC=gcc
CFLAGS=-Wall -ansi -pedantic -D_DEFAULT_SOURCE
#CFLAGS=-g -Wall -ansi -pedantic -D_DEFAULT_SOURCE -DDEBUG
src=$(wildcard *.c)
obj=$(src:.c=.o)

all: bjcgrep

%.o:	%.c
	$(CC) $(CFLAGS) -c $^ -o $@

bjcgrep:	$(obj)
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm -f $(obj) bjcgrep
