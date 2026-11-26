all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

examples: all
	rocq makefile -f _CoqProject.examples -docroot examples -o Makefile-examples.coq
	$(MAKE) -k -f Makefile-examples.coq

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	-$(MAKE) -f Makefile-examples.coq clean 2>/dev/null
	rm -f Makefile-examples.coq Makefile-examples.coq.conf

.PHONY: all examples clean
