Version 3.4.2
-------------

* ensured compatibility from Coq 8.7 to 8.11

Version 3.4.1
-------------

* ensured compatibility from Coq 8.7 to 8.10

Version 3.4.0
-------------

* moved to Flocq 3.0; minimal Coq version is now 8.7
* added support for `Ztrunc`, `Zfloor`, etc
* added support for constants written using `bpow radix2`

Version 3.3.0
-------------

* added option `i_integral_width` for absolute width of integrals
* added option `i_native_compute` to use `native_compute` instead of `vm_compute`
* added option `i_delay` to avoid immediate check (mostly useful for `interval_intro`)
* improved accuracy for interval `cos` and `sin` away from zero
* ensured compatibility from Coq 8.5 to Coq 8.7

Version 3.2.0
-------------

* added support for some improper integrals using `RInt_gen`

Version 3.1.1
-------------

* ensured compatibility with Coq 8.6

Version 3.1.0
-------------

* improved tactic so that it can be used with backtracking tacticals (`try`, `||`)
* fixed ineffective computation of integrals with reversed or overlapping bounds

Version 3.0.0
-------------

* added support for integrals using Coquelicot's `RInt` operator
* improved support for Taylor models

Version 2.2.1
-------------

* moved to MathComp 1.6

Version 2.2.0
-------------

* improved tactic so that it handles goals with non floating-point bounds
* added a dependency on Coquelicot to remove an assumption about `ln`

Version 2.1.0
-------------

* moved to Flocq 2.5

Version 2.0.0
-------------

* added support for Taylor models (`i_bisect_taylor`)
* added support for `ln`
* improved tactic so that it handles hypotheses with non floating-point bounds

Version 1.1.0
-------------

* moved to Flocq 2.4
* added support for disequalities to the tactic
* added support for the `PI` symbol
* enlarged the domain of the interval versions of `cos` and `sin`

Version 1.0.0
-------------

* removed remaining axioms

Version 0.16.2
--------------

* fixed install rule on case-insensitive filesystems

Version 0.16.1
--------------

* removed the custom definition of `atan` and used the one from Coq 8.4

Version 0.16.0
--------------

* switched build system to `remake`
* moved to Coq 8.4

Version 0.15.1
--------------

* fixed failures when combining `interval_intro` with `i_bisect*`

Version 0.15.0
--------------

* added support for strict inequalities to the tactic
* added support for integer power to the tactic
* improved support for absolute value in the tactic
* improved tactic so that it directly handles `e1 <= e2`

Version 0.14.0
--------------

* sped up square root for `Z`-based floating-point numbers
* improved readability of the error messages for the tactic
* modularized the tactic so that other specializations are available to user code
* moved to Flocq 2.0

Version 0.13.0
--------------

* moved to Coq 8.3

Version 0.12.1
--------------

* fixed an incompatibility with Flocq 1.2

Version 0.12
------------

* added a dependency on the Flocq library

Version 0.11
------------

* removed `i_nocheck` parameter as computations are no longer done at `Qed` time
