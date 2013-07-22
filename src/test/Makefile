INCLUDES= -I ../src/datastructure -I ../src/calculus
DEPENDENCY= oUnit str unix
OCAMLFIND=ocamlfind
OCAMLFIND_FLAGS= -package "$(DEPENDENCY)" -linkpkg $(INCLUDES)

test-szs.o:
	$(OCAMLFIND) ocamlopt  $(OCAMLFIND_FLAGS) -o $@ ../src/datastructure/szs.ml \
		datastructure/szs_test.ml

test-subprover.o:
	$(OCAMLFIND) ocamlopt  $(OCAMLFIND_FLAGS) -o $@ ../src/calculus/subprover.mli \
		../src/calculus/subprover.ml calculus/subprover_test.ml


all: test-szs.o test-subprover.o

depend:
	$(OCAMLFIND) ocamldep

clean:
	rm test-szs.o
	rm test-subprover.o

.PHONY: clean
