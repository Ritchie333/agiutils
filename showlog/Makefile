CC = clang
CFLAGS = -g
LIBS = 
%.o: %.c
	${CC} ${CFLAGS} -c $<

all: showlog

clean:
	rm showlog showlog.o

showlog: showlog.o
	${CC} ${LIBS} $< -o $@