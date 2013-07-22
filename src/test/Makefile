INCLUDES= -I ../datastructure -I ../calculus
DEPENDENCY= oUnit str unix
OCAMLFIND=ocamlfind
FLAGS= -package "$(DEPENDENCY)" -linkpkg $(INCLUDES)


build-test:
	$(OCAMLFIND) ocamlopt $(FLAGS) -o test-subprover \
	../datastructure/szs.mli  ../datastructure/szs.ml \
	../calculus/subprover.mli ../calculus/subprover.ml \
	calculus/subprover_test.ml

clean:
	rm test-szs.o
	rm test-subprover.o

.PHONY: clean
