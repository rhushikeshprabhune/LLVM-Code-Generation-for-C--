

.SUFFIXES: %.cpp

OBJS =  main.o \
	cmm.y.o  \
	cmm.lex.o \
	list.o \
	symbol.o \
	cmdline.lex.o

.PHONY: tests test all

all: p2

p2: $(OBJS)
	clang++ -g -Wno-implicit-function-declaration -o $@ $(OBJS) `llvm-config --cxxflags --ldflags --libs` -ly -ll `llvm-config --system-libs`

clean:
	rm -Rf p2 $(OBJS) cmm.y.cpp cmm.lex.cpp cmm.y.hpp cmdline.lex.cpp 
	make -C ./tests clean

test: tests

tests: p2
	make -C ./tests test

%.o:%.cpp
	clang++ -g -c -o $@ $< `llvm-config --cxxflags` 

cmdline.lex.cpp: cmdline.lex
	flex -PCmd -o$@ cmdline.lex 

cmm.y.cpp: cmm.y
	bison -d -o $@ $<

cmm.y.hpp: cmm.y.cpp

cmm.lex.cpp: cmm.lex
	flex -o$@ $<

list.cpp: list.h 

symbol.cpp:symbol.h uthash.h

%:%.o
%:%.cpp
