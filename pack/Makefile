OPAMDIR   := $(shell opam config var lib)
ZARITHDIR := $(OPAMDIR)/zarith
OCB = ocamlbuild

all: main.ml
	$(OCB) main.native

clean:
	$(OCB) -clean

exec:
	dune build main.exe && time ./_build/default/main.exe
