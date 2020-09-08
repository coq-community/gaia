# Gaia

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/palmskog/gaia/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/palmskog/gaia/actions?query=workflow%3ACI




Implementation of books from N. Bourbaki's Elements of Mathematics
in Coq using the Mathematical Components library, including set theory
and number theory.

## Meta

- Author(s):
  - José Grimm
  - Alban Quadrat
  - Carlos Simpson
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [MathComp ssreflect 1.11.0](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
- Coq namespace: `gaia`
- Related publication(s):
  - [Implementation of Bourbaki's Elements of Mathematics in Coq: Part One, Theory of Sets](https://jfr.unibo.it/article/view/1899) doi:[10.6092/issn.1972-5787/1899](https://doi.org/10.6092/issn.1972-5787/1899)
  - [Implementation of Bourbaki's Elements of Mathematics in Coq: Part Two, From Natural Numbers to Real Numbers](https://jfr.unibo.it/article/view/4771) doi:[10.6092/issn.1972-5787/4771](https://doi.org/10.6092/issn.1972-5787/4771)
  - [Implementation of Bourbaki's Elements of Mathematics in Coq: Part One, Theory of Sets](https://hal.inria.fr/inria-00408143) 
  - [Implementation of Bourbaki's Elements of Mathematics in Coq: Part Two; Ordered Sets, Cardinals, Integers](https://hal.inria.fr/inria-00440786) 
  - [Implementation of Bourbaki's Elements of Mathematics in Coq: Part Three Structures](https://hal.inria.fr/hal-01412037) 
  - [Fibonacci numbers and the Stern-Brocot tree in Coq](https://hal.inria.fr/hal-01093589) 
  - [Implementation of three types of ordinals in Coq](https://hal.inria.fr/hal-00911710) 

## Building instructions

``` shell
git clone https://github.com/palmskog/gaia
cd gaia
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

Gaia stands for: Geometry, Algebra, Informatics and Applications.
More information about the project is available at the [project website][gaia-url].

[gaia-url]: http://www-sop.inria.fr/marelle/gaia/
