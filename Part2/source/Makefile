CPPFLAGS += -I/usr/local/pccts-1.33/include -I/usr/include/pccts
CXXFLAGS += -Wno-write-strings
#CXXFLAGS += -g

all: cl

cl: cl.o codegen.o codegest.o ptype.o semantic.o symtab.o scan.o err.o util.o
	$(CXX) -o $@ $^

cl.c err.c parser.dlg tokens.h: cl.g
	antlr -gt $<

mode.h scan.c: parser.dlg
	dlg -ci $< scan.c

cl.o: cl.c mode.h tokens.h myASTnode.hh
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

codegen.o codegest.o ptype.o semantic.o symtab.o util.o: %.o: %.cc %.hh myASTnode.hh
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

scan.o err.o: %.o: %.c
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

clean:
	@$(RM) core* cl cl.o codegen.o codegest.o err.o ptype.o scan.o semantic.o \
		symtab.o util.o cl.c err.c mode.h parser.dlg scan.c tokens.h

jps := $(sort $(wildcard jp?)) $(sort $(wildcard jp??))

test_1:
	@cp ../jps/jps1/* . ;
	@cp ../sjps/* .

test_2:
	@cp ../jps/jps2/* . ;
	@cp ../sjps/* .

test_all:
	@cp ../jps/jps1/* . ;
	@cp ../jps/jps2/* . ;
	@cp ../sjps/* .
	
test_clean:
	@$(RM) output jp* sjp*

diff: cl
	@for i in $(jps); do \
		echo $$i; \
		./cl execute < $$i > output; \
		diff s$$i output; \
	done
	@$(RM) output jp* sjp*
