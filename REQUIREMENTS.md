
# Software Requirements

The project builds with [Coq](https://coq.inria.fr/) version `8.16.1`. It depends on the opam package `coq-smpl` and `coq-equations` (version 1.3 at least). After installing [opam](https://opam.ocaml.org/) with your favorite package manager, the proper environment is setup and installed with
```
opam init
eval $(opam env)
opam install coq.8.16.1 coq-equations.1.3+8.16 coq-smpl.8.16
```

Alternatively, a `Dockerfile` is provided for [docker](https://docs.docker.com/) image setup.

# Hardware Requirements

The projects takes several minutes to compile on a recent laptop (4GHz processor, 8GB RAM). Less than 2GB of RAM is not recommended.
