VERSION = 1.0
SHELL = /bin/sh

CC = g++
CFLAGS = -std=c++11 -O3 -Wall -Wextra -pedantic -funroll-loops
#CFLAGS = -std=c++11 -g -Wall -Wextra -pedantic -funroll-loops -DNDEBUG
OBJS = utils.o mmsearch_v17.o main.o

EXEC = clean matchstat

.cpp.o:
	$(CC) $(CFLAGS) -c $<

all: $(EXEC)

matchstat: $(OBJS)
	$(CC) $(CFLAGS) -o matchstat $(OBJS) $(LIBS)

clean:
	/bin/rm -f matchstat *.o
