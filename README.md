# Introduction

This collection of GAP files allows basic symbolic computation in free multiplicative conic alternative algebras (over free commutative rings, that is, polynomial rings).
In other words, it provides a framework to prove that certain identities hold in any multiplicative conic alternative algebra over any commutative ring by deriving these identities from a set of known identities in such objects.
It also supports similar computations in the Lie algebra and the group of automorphisms that are constructed in the preprint \[DMW25\] "Name" (arXiV link) from an arbitrary multiplicative conic alternative algebra.
It cannot prove any such identity (which seems to be a hopeless task), but it is powerful enough to prove all identities that are needed in \[DMW25\].

# Installation

Blabla download and read `read.g`. Modify `ComRing_rank`, `ConicAlg_rank` and `Trace_MaxLength` according to your wishes. It is recommended to not change the value of `ComRing_rank` (it should be high enough for most purposes and decreasing it does not improve the runtime significantly) and to either keep the values `ConicAlg_rank := 2`, `Trace_MaxLength := 5` or to change them to `ConicAlg_rank := 4`, `Trace_MaxLength := 4`.

# User interface

Usage examples may also be found in the file `test/test_basic.txt`.

## Indeterminates in the rings

The symbols `t1, t2, ...` denote arbitrary elements of the (arbitrary) commutative ring over which we work and `a1, a2, ...` denote arbitrary elements of the (arbitrary) multiplicative conic alternative algebra. We refer to these elements as *indeterminates*. The available number of such indeterminates of each type is determined by the variables `ComRing_rank` and `ConicAlg_rank`, respectively, which may be modified by the user before reading the files (see [[Installation]]). The indeterminates may be accessed by `ComRingIndet(i)` and by `ConicAlgIndet(i)` where `i` is the number of the desired indeterminate, or alternatively as the values of the predefined constants `t1, t2, ...` and `a1, a2, ...`.

The symbols `g1, g2, g3` denote the (arbitrarily chosen) constants $ \gamma_1, \gamma_2, \gamma_3 $ in the commutative ring. They may be accessed by `ComRingGamIndet(i)`, or alternatively as the values of the predefined constants `g1, g2, g3`.

Sums and products in the commutative ring and in the conic algebra can be computed by the usual GAP operations `+` and `*`, and inverses of elements of the commutative ring (but not of the conic algebra) may be computed using `^-1`. Taking the inverse of a ring element implictly introduces the assumption that it is indeed invertible. In practice, we will only have to use the inverses of `g1, g2, g3`, and this only in situations in which they are indeed assumed to be invertible.

## Conic algebra structure

Let `a` be an element of the conic algebra. Then the conjugate of `a`, which is again an element of the conic algebra, is printed as `a'` and may be computed using `ConicInv(a)` (refering to the fact the conjugation map is an involution). The norm and trace of `a`, which are elements of the commutative ring, are printed as `n(a)` and `tr(a)` and may be computed using `ConicNorm(a)` and `ConicTr(a)`. For another conic algebra element `b`, the evaluation of the linearisation of the norm at `(a,b)` may be computed using `ConicNormLin(a,b)`. It is a known fact that `ConicNormLin(a,b) = tr(a'b)` holds in any multiplicative conic alternative algebra.

Several measures are taken to simplify (the display of) traces. Multiplication signs in the argument of the trace are not printed: For `a=a1*a2`, the trace of `a` is printed as `tr(a1a2)`. By the relation `tr((xy)z) = tr(x(yz))`, we can often omit brackets, so the result of `ConicTr((a1*a2)*a3)`is printed as `tr(a1a2a3)`. Using in addition the relations `tr(x') = tr(x)` and `tr(xy) = tr(yx)`, the arguments of the trace are often permuted and/or replaced by their conjugates to ensure proper cancellation of terms. For example, both `ConicTr(a1*ConicInv(a2))` and `ConicTr(ConicInv(a1)*a2)` are printed as `tr(a1a2')`, and `ConicTr(ConicInv(a1)*a2*a3)` is printed as `tr(a1a3'a2')` (because `tr(a1'a2a3) = tr((a1'a2a3)') = tr(a3'a2'a1) = tr(a1a3'a2')`).

# Verification of the claims in \[DMW25\]

# License
