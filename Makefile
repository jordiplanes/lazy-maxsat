CFLAGS=-O3 #-mtune=opteron
CPPFLAGS=-O3 #-mtune=opteron
TARGETS=lazy.wcnf.bare lazy.wcnf.lb lazy.wcnf.cuc lazy.wcnf.acc lazy.wcnf.lb-cuc lazy.wcnf.lb-acc lazy.wcnf

all: $(TARGETS)

lazy.wcnf.bare:
	g++ -O3 lazy_weighted_fast.cc -o lazy.wcnf.bare

lazy.wcnf.lb:
	g++ -O3 -DLB4 lazy_weighted_fast.cc -o lazy.wcnf.lb

lazy.wcnf.cuc:
	g++ -O3 -DCUC_RULE lazy_weighted_fast.cc -o lazy.wcnf.cuc

lazy.wcnf.acc:
	g++ -O3 -DRESOLUTION_RULE lazy_weighted_fast.cc -o lazy.wcnf.acc

lazy.wcnf.lb-cuc:
	g++ -O3 -DLB4 -DCUC_RULE lazy_weighted_fast.cc -o lazy.wcnf.lb-cuc

lazy.wcnf.lb-acc:
	g++ -O3 -DLB4 -DRESOLUTION_RULE lazy_weighted_fast.cc -o lazy.wcnf.lb-acc

lazy.wcnf:
	g++ -O3 -DLB4 -DRESOLUTION_RULE -DCUC_RULE lazy_weighted_fast.cc -o lazy.wcnf

lazy: lazy.o borchers.o
	g++ lazy.o borchers.o -o lazy

lazy_weighted: lazy_weighted.o weighted_borchers.o
	g++ lazy_weighted.o weighted_borchers.o -o lazy_weighted

clean:
	$(RM) $(TARGETS)

tgz: 
	tar zcvf lazy.tgz *.c *.cc *.h Makefile

