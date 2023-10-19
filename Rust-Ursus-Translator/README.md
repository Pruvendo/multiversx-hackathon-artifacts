# Translator: rust -> ursus
## Script for generating Ursus project from Everscale solidity project (using ast)


## Dependencies (make sure that you don't have io, system packcges on opam list!):
1. coq-io https://github.com/Pruvendo/coq-io.git (automatically installed by ```make install```)
2. coq-json https://github.com/Pruvendo/coq-json.git (automatically installed by ```make install```)
3. system https://github.com/Pruvendo/coq-system.git (automatically installed by ```make install```)
4. rust-ast generator 
5. Make
6. coq
7. dune

## Building
```bash
make build
```
## Installing
```bash
opam install .
```

## Use 
```bash
rust_ursus_tr path/to/rust/ast
```
