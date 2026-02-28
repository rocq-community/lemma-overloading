<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Lemma Overloading

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/lemma-overloading/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/lemma-overloading/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://coq-community.org/lemma-overloading

[doi-shield]: https://zenodo.org/badge/DOI/10.1017/S0956796813000051.svg
[doi-link]: https://doi.org/10.1017/S0956796813000051

This project contains Hoare Type Theory libraries which
demonstrate a series of design patterns for programming
with canonical structures that enable one to carefully
and predictably coax Coq's type inference engine into triggering
the execution of user-supplied algorithms during unification, and
illustrates these patterns through several realistic examples drawn
from Hoare Type Theory. The project also contains typeclass-based
re-implementations for comparison.

## Meta

- Author(s):
  - Georges Gonthier (initial)
  - Beta Ziliani (initial)
  - Aleksandar Nanevski (initial)
  - Derek Dreyer (initial)
- Rocq-community maintainer(s):
  - Anton Trunov ([**@anton-trunov**](https://github.com/anton-trunov))
- License: [GNU General Public License v3.0 or later](LICENSE.md)
- Compatible Rocq/Coq versions: 9.0 or later (use releases for other Rocq/Coq versions)
- Additional dependencies:
  - [Hierarchy Builder](https://github.com/math-comp/hierarchy-builder) 1.7.0 or later
  - [MathComp](https://math-comp.github.io) 2.4.0 or later (`ssreflect` suffices)
- Rocq/Coq namespace: `LemmaOverloading`
- Related publication(s):
  - [How to make ad hoc proof automation less ad hoc](https://software.imdea.org/~aleks/papers/lessadhoc/journal.pdf) doi:[10.1017/S0956796813000051](https://doi.org/10.1017/S0956796813000051)
  - [Structuring the verification of heap-manipulating programs](https://software.imdea.org/~aleks/papers/reflect/reflect.pdf) doi:[10.1145/1706299.1706331](https://doi.org/10.1145/1706299.1706331)

## Building and installation instructions

The easiest way to install the latest released version of Lemma Overloading
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-lemma-overloading
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/coq-community/lemma-overloading.git
cd lemma-overloading
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Files described in the paper

The Coq source files mentioned in the paper [How to make ad hoc proof automation less ad hoc][lessadhoc],
Journal of Functional Programming 23(4), pp. 357-401, are described below. See also the
[coqdoc presentation][coqdoc] of the files from the latest release.

### `indom.v`

This file contains the indomR lemma from Section 3 "A simple overloaded lemma"

### `terms.v`, `xfind.v`, `cancel.v`, `cancelD.v`, `cancel2.v`

These files prove the `cancelR` lemma from Section 4 "Reflection: Turning
semantics into syntax". The first one contains the abstract syntax for heaps
along with the lemma `cancel_sound`. `xfind.v` has the xfind structure
to find an element in a list, return its index, and extend the list if the
element is not found. The file `cancel.v` has the main overloaded lemma `cancelR`.
Finally, `cancelD.v` contains the `simplify` lemma from section 4.3 and `cancel2.v`
contains an alternative version of the cancellation function without using
reflection.
 
### `stlogR.v`

File containing a whole bunch of overloaded lemmas to automate the verification
of imperative programs using Hoare Type Theory. The main technicalities in this
file are covered in Section 5 "Solving for functional instances".

### `noalias.v`

File containing all the automated lemmas described in Section 6 "Flexible
composition and application of overloaded lemmas".


## Bonus track

The files below didn't make it to the paper but deserve attention.

### `auto.v`

This file contains an adapted example from VeriML (Stampoulist and Shao),
to automatically prove propositions in a logic with binders.

### `llistR.v`

Verification of a linked list datatype using the "step" overloaded lemma described in Section 5.2.

### `noaliasBT.v`

There are several ways to attack a problem.
Some of them lead to interesting but yet not entirely satisfactory results.
Here are two versions of the `noalias` overloaded lemma with a different look.

### `indomCTC.v`, `xfindCTC.v`, `cancelCTC.v`, `noaliasCTC.v`, `stlogCTC.v` 

These files contains the same automated lemmas as in the files `indom`, `cancel`,
`noalias` and `stlogR`, but done with Coq Type Classes. 

## Other files

The files not mentioned above are part of the HTT library,
introduced in the paper [Structuring the Verification of Heap-Manipulating Programs][reflect],
Proceedings of the Symposium on Principles of Programming Languages (POPL) 2010,
pp. 261-274.

[lessadhoc]: https://software.imdea.org/~aleks/papers/lessadhoc/journal.pdf
[reflect]: https://software.imdea.org/~aleks/papers/reflect/reflect.pdf
[coqdoc]: https://coq-community.github.io/lemma-overloading/docs/latest/coqdoc/toc.html
