.PHONY: default build install uninstall test clean demo1 demo2

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

demo1:
	dune exec -- matchers_demo

demo2:
	dune exec -- zipper_antimirov_demo

clean:
	dune clean
