CC = clang
CFLAGS = -g
LIBS = 
%.o: %.c
	${CC} ${CFLAGS} -c $<

all: volx

clean:
	rm volx volx.o

volx: volx.o
	${CC} ${LIBS} $< -o $@