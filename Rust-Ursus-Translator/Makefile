all: build

opam:
	dune build && cd _build/default/ && ocamlbuild main.native -use-ocamlfind -package io-system

install:
	mkdir _tmp
	cd _tmp/   			&& git clone https://github.com/Pruvendo/coq-io.git
	cd _tmp/coq-io 			&& opam install . -y
	cd _tmp/   			&& git clone https://github.com/Pruvendo/coq-system.git
	cd _tmp/coq-system 		&& opam install . -y
	cd _tmp/ 			&& git clone https://github.com/Pruvendo/coq-json.git
	cd _tmp/coq-json 	&& opam install . -y
	rm -rf _tmp

build:
	dune build && cd _build/default/ && ocamlbuild main.native -use-ocamlfind -package io-system

clean:
	dune clean
