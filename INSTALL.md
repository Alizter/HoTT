## Introduction

The HoTT library is library for the Coq proof assistant<!-- TODO: link -->. The
Coq proof assistant is written in OCaml<!-- TODO: link -->. OPAM (the Ocaml
PAcakage Manager) is the recommended way to install Coq and the dune build
system<!-- TODO: Link here! -->, the build system used to build the library.


## Prerequisites

### Installing OPAM

First, you need to install OPAM.

* To do this in Debian or any distribution with `apt-get` run
```
$ sudo apt-get update
$ sudo apt-get install opam
```
* On macOS it is recommended that you use the brew package manager to install OPAM:
```
$ brew update
$ brew install opam
```
* TODO: Windows

OPAM is a package manager for OCaml. We first need to initialize it by:
```
$ opam init
```
It is recommended to allow OPAM to change your .profile file when it
asks for permission.

It is recommended that you create a switch for your OCaml version. You can do
this in the following way:
```
$ opam switch create 4.07.1
$ opam switch 4.07.1
```
This will install OCaml 4.07.1 (or whatever version you used) in a
switch. Switches can be useful as they allow you to easily switch between
different versions of packages.

After the switch has been installed OPAM will ask you to update the opam
environment. This will allow you to access any programs OPAM installs.
```
$ eval $(opam env)
```

### Installing Coq

You need to install the Coq proof assistant version 8.12 or above. This can be
done with the following:
```
$ opam install coq
```
OPAM will install all the necessery dependencies for you.

### Installing Dune

The HoTT library is built with the dune build system. This can be installed with
OPAM:
```
$ opam install 
```

## Building the HoTT library

Now that we have OPAM, Coq and Dune installed we can build the main HoTT
library.

Using git you may clone the repo:
```
$ git clone https://github.com/HoTT/HoTT.git
```

Now change your working directory to the HoTT folder:
```
$ cd HoTT
```

You can now build the library using dune:
```
$ dune build
```

If you want to see which files are being built, you can pass the following `--display`
argument to dune:
```
$ dune build --display short
```

Once that has finished you can use your favourite IDE to step through the
files. 

## Setting up an IDE

### Coqide

Coqide is the recommended way to browse coq files. You can install it using
opam:
```
$ opam install coqide
```

### Emacs + Proof General (PG)

Proof General should be able to read the _CoqProject file and set up
accordingly.

### Visual Studio Code

TODO: Support for visual studio code

### Vim

TODO: Support for vim

## Browsing the library

You should be able to open a `.v` file in the `theories/`
directory. Note Dune will automagically build all `.v` files in `theories/`.


In case of any problems, feel free to contact us by opening an issue at
https://github.com/HoTT/HoTT.
