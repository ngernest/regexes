.PHONY: default build install uninstall test clean

default:
	dune build

build:
	dune build

install:
	opam update
	opam install --yes . --deps-only

uninstall:
	dune uninstall	

test:
	dune runtest 

clean:
	dune clean

