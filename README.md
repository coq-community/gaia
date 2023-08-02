<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Gaia

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/gaia/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/gaia/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



Implementation of books from N. Bourbaki's Elements of Mathematics
in Coq using the Mathematical Components library, including set theory
and number theory.

## Meta

- Author(s):
  - José Grimm
  - Alban Quadrat
  - Carlos Simpson
- Coq-community maintainer(s):
  - Laurent Théry ([**@thery**](https://github.com/thery))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [MathComp ssreflect 2.0 or later](https://math-comp.github.io)
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

## Building and installation

To build and install manually, do:

``` shell
git clone https://github.com/coq-community/gaia.git
cd gaia
make   # or make -j <number-of-cores-on-your-machine> 
make install
```

## Documentation

Gaia stands for: Geometry, Algebra, Informatics and Applications.
More information about the project is available at the [project website][gaia-url].

[gaia-url]: http://www-sop.inria.fr/marelle/gaia/
