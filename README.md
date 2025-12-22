# Introduction

This collection of GAP files allows basic symbolic computation in free multiplicative conic alternative algebras (over free commutative rings, that is, polynomial rings).
In other words, it provides a framework to prove that certain identities hold in any multiplicative conic alternative algebra over any commutative ring by deriving these identities from a set of known identities in such objects.
It also supports similar computations in the Lie algebra and the group of automorphisms that are constructed in the preprint \[DMW\] *Cubic norm pairs and $G_2$- and $F_4$-graded groups and Lie algebras* (TODO: arXiv link) from an arbitrary multiplicative conic alternative algebra.
It cannot prove any such identity (which seems to be a hopeless task), but it is powerful enough to prove all identities that are needed in \[DMW\].

# Installation

GAP version at least ... 
It has been tested with GAP version 4.15.1.

Blabla download and read `read.g`. Modify `ComRing_rank`, `ConicAlg_rank` and `Trace_MaxLength` according to your wishes. It is recommended to not change the value of `ComRing_rank` (it should be high enough for most purposes and decreasing it does not improve the runtime significantly) and to either keep the values `ConicAlg_rank := 2`, `Trace_MaxLength := 5` or to change them to `ConicAlg_rank := 4`, `Trace_MaxLength := 4`.

## Windows

## Unix

# Verification of the claims in \[DMW\]

# User interface

Usage examples may also be found in the file `test/test_basic.txt`.

## Indeterminates in the rings

The symbols `t1, t2, ...` denote arbitrary elements of the (arbitrary) commutative ring over which we work and `a1, a2, ...` denote arbitrary elements of the (arbitrary) multiplicative conic alternative algebra.
We refer to these elements as *indeterminates*.
The available number of such indeterminates of each type is determined by the variables `ComRing_rank` and `ConicAlg_rank`, respectively, which may be modified by the user before reading the files (see [Installation]).
The indeterminates may be accessed by `ComRingIndet(i)` and `ConicAlgIndet(i)` where `i` is the number of the desired indeterminate, or alternatively as the values of the predefined constants `t1, t2, ...` and `a1, a2, ...`.

In this documentation, we will refer to the commutative ring and to the multiplicative conic alternative algebra by $k$ and $C$. Internally, they are called `ComRing` and `ConicAlg`.

The (arbitrarily chosen) constants $ \Gamma =(\gamma_1, \gamma_2, \gamma_3) \in k^3 $ are printed as `g1, g2, g3`.
They may be accessed by `ComRingGamIndet(i)`, or alternatively as the values of the predefined constants `g1, g2, g3`.

Sums and products in $k$ and $C$ can be computed by the usual GAP operations `+` and `*`, and inverses of elements of the commutative ring (but not of the conic algebra) may be computed using `^-1`. Taking the inverse of a ring element implictly introduces the assumption that it is indeed invertible. In practice, we will only have to use the inverses of `g1, g2, g3`, and this only in situations in which they are indeed assumed to be invertible.

## The conic algebra structure

Let `a` be an element of $C$.
Then the conjugate of `a`, which is again an element of $C$, is printed as `a'` and may be computed using `ConicInv(a)` (referring to the fact the conjugation map is an involution).
The norm and trace of `a`, which are elements of $k$, are printed as `n(a)` and `tr(a)` and may be computed using `ConicNorm(a)` and `ConicTr(a)`.
For another conic algebra element `b`, the evaluation of the linearisation of the norm at `(a,b)` may be computed using `ConicNormLin(a,b)`.
It is a known fact that `ConicNormLin(a,b) = tr(a'b)` holds in any multiplicative conic alternative algebra.

Several measures are taken to simplify (the display of) traces.
Multiplication signs in the argument of the trace are not printed:
For `a=a1*a2`, the trace of `a` is printed as `tr(a1a2)`.
By the relation `tr((xy)z) = tr(x(yz))`, we can often omit brackets, so the result of `ConicTr((a1*a2)*a3)`is printed as `tr(a1a2a3)`.
Using in addition the relations `tr(x') = tr(x)` and `tr(xy) = tr(yx)`, the arguments of the trace are often permuted and/or replaced by their conjugates to ensure proper cancellation of terms.
For example, both `ConicTr(a1*ConicInv(a2))` and `ConicTr(ConicInv(a1)*a2)` are printed as `tr(a1a2')`, and `ConicTr(ConicInv(a1)*a2*a3)` is printed as `tr(a1a3'a2')` (because `tr(a1'a2a3) = tr((a1'a2a3)') = tr(a3'a2'a1) = tr(a1a3'a2')`).

## The cubic Jordan matrix algebra

### Elements of the cubic Jordan matrix algebra

Let `a` be an element of $C$, let `t` be an element of $k$, let `i` be `1`, `2` or `3` and let `i, j, l` denote the unique cyclic permutation of `1, 2, 3` starting with `i`.
Then the elements of the cubic Jordan matrix algebra $J = J' = Her_3(k, C, \Gamma)$ that are denoted in \[DMW\] by $a[ij]$ and $te_i$ can be constructed as `CubicConicEl(a, i)` and `CubicComEl(t, i)` and are printed as `a[ij]` and `t[ii]`, respectively.
Recall that `a[ji]` is defined to be `a'[ij]`, so `a[pq]` is defined for all distinct `p, q` in `[1, 2, 3]`.
For arbitrary distinct `i, j` in `[1, 2, 3]` and `b` from $C$ or $k$, the expression `CubicElMat(b, i, j)` evaluates to the element `b[ij]` if it exists, and throws an error otherwise.

Arbitrary elements of $J$ may be constructed as sums of the "basic" elements described above.
Alternatively, the element `t[11] + s[22] + r[33] + a[23] + b[31] + c[12]` may be constructed as `CubicElFromTuple(t, s, r, a, b, c)`.

Let `cub = t[11] + s[22] + r[33] + a[23] + b[31] + c[12]` be an arbitrary element of $J$.
Then the components of `cub` may be accessed by `CubicConicPart(cub, i)` and `CubicComPart(cub, i)`.
For example, `CubicConicPart(cub, 1) = a` and `CubicComPart(cub, 2) = s`.

### The Jordan algebra structure

Let `a, b, c` be elements of $J$. The Jordan algebra operators of $J$ can be computed as follows: `JordanU(a,b)` is $U_a(b)$, `JordanULin(a,b,c)` is the linearisation $U_{a,b}(c)$ and `JordanD(a,b,c)` is $D_{a,b}(c) = \{ a, b, c \} = U_{a,c}(b)$. 

## The Brown algebra

We refer to the $k$-module $B = (k, J, J', k)$ as the *Brown algebra* because if $2$ is invertible in $k$, then it has the structure of a structurable algebra that is known under this name.
It parametrises the $1$- and $(-1)$-parts of the Lie algebra that we construct in \[DMW\].
The element `[ t, cub1, cub2, s ]` of $B$ may be constructed as `BrownElFromTuple(t, cub1, cub2, s)`.

Let `brown` be an element of $B$. While `brown` is internally represented as a list, it is itself not a list in GAP, so `brown[1]` throws an error. The underlying 4-element list which describes `brown` may be accessed as `BrownElTuple(brown)`. Further, `BrownElPart(brown, i) = BrownElTuple(brown)[i]` for `i` in `[1, 2, 3, 4]`. We also define `BrownElComPart(brown, 1) = BrownElPart(brown, 1)`, `BrownElComPart(brown, 2) = BrownElPart(brown, 4)`, `BrownElConicPart(brown, 1) = BrownElPart(brown, 2)` and `BrownElConicPart(brown, 2) = BrownElPart(brown, 3)`.

## The Lie algebra

The Lie algebra $L$ that we construct from $J$ is, as a $k$-module, the direct sum $\bigoplus_{i=-2}^2 L_i$. We refer to it as `Lie` in the documentation and in our naming conventions. For arbitrary elements `lie1`, `lie2`, their sum may be computed as `lie1 + lie2` and their Lie bracket as `lie1 * lie2`. For `lie` in $L$ and `t` in $k$, the scalar multiplication of `lie` by `t` may be computed as `t * lie`.

### $L_{-2}$ and $L_2$

The $k$-submodules $L_{-2}$ and $L_2$ are isomorphic to $k$. Their generators are denoted by $x$ and $y$ in \[DMW\]. They are printed as `x` and `y`, and may be accessed as the constants `LieX` and `LieY`.

For an arbitrary element `lie` of $L$, the elements `t` and `s` of $k$ for which `t*LieX` and `s*LieY` are the components of `lie` in $L_{-2}$ and $L_{-1}$ may be accessed as `LiePart(lie, -2)` and `LiePart(lie, 2)`, respectively.

### $L_{-1}$ and $L_1$

The $k$-submodules $L_{-1}$ and $L_1$ are isomorphic to the Brown algebra $B$. However, we strictly distinguish between elements of $B$, $L_{-1}$ and $L_1$. For an element `brown` of $B$, the corresponding elements of $L_{-1}$ and $L_1$ may be constructed as `BrownNegToLieEmb(brown)` and `BrownPosToLieEmb(brown)`, respectively. We also provide the shorthand `LieBrownPosElFromTuple(a, t, s, b) := BrownPosToLieEmb(BrownPosElFromTuple(a, t, s, b))`, and a similar shorthand `LieBrownNegElFromTuple`.

The element `lie := BrownPosToLieEmb(brown)` is printed as `brown_+`, and `lie := BrownNegToLieEmb(brown)` is printed as `brown_-`. For example, `[ t1, a1[23], a2[12], t1+t2 ]_+` is an element of $L_1$.

For an arbitrary element `lie` of $L$, the elements `brownNeg` and `brownPos` of $B$ for which `BrownNegToLieEmb(brownNeg)` and `BrownPosToLieEmb(brownPos)` are the components of `lie` in $L_{-1}$ and $L_{1}$ may be accessed as `LiePart(lie, -1)` and `LiePart(lie, 1)`, respectively.

### The Lie subalgebra $L_0$

The subalgebra $L_0$ of $L$ is itself the direct sum of three components $L_{0,-1}, Z, L_{0,1}$. We internally distinguish between elements of $L_0$ and elements of $L$, and the function `L0ToLieEmb` describes the corresponding embedding.

#### $L_{0,-1}$ and $L_{0,1}$

The $k$-submodules $L_{0,-1}$ and $L_{0,1}$ are isomorphic to the cubic Jordan matrix algebra $J$. For an element `cub` of $J$, the corresponding elements of $L_{0,-1}$ and $L_{0,1}$ may be constructed as `CubicNegToLieEmb(cub)` and `CubicPosToLieEmb(cub)`, respectively. Note that we strictly distinguish between elements of $J$, $L_{0,-1}$ and $L_{0,1}$.

The element `lie := CubicPosToLieEmb(cub)` is printed as `ad_{cub}^+`, and `lie := CubicNegToLieEmb(cub)` is printed as `ad_{cub}^-`. For example, `ad_{a1[23]}^+` is an element of $L_{0,1}.

For an arbitrary element `lie` of $L$, the elements `brownNeg` and `brownPos` of $B$ for which `BrownNegToLieEmb(brownNeg)` and `BrownPosToLieEmb(brownPos)` are the components of `lie` in $L_{-1}$ and $L_{1}$ may be accessed as `LiePart(lie, -1)` and `LiePart(lie, 1)`, respectively.

#### $Z$ and `DD`

We refer to the $k$-module $\langle \mathbf{d}_{a,b} \mid a \in J, b \in J' \rangle$ (which is unnamed in \[DMW\]) as `DD` in (the documentation of) this GAP package. The $k$-module $L_0$, denoted by `L0` in the code, is the (not necessarily direct) sum of `DD` with $k \xi + k\zeta$.

The elements $\xi$ and $\zeta$ are printed as `xi` and `zeta`, and they may be accessed by the constants `LieXi` and `LieZeta`, respectively.
An element $\mathbf{d}_{a,b}$ is printed as `dd_{a,b}`, and it may be constructed as `dd(a, b)`.

While this should usually not be relevant for the end user, we note that we internally distinguish between elements of `DD`, $L_0$ and $L$. The elements `DDdd(a, b)`, `L0dd(a, b)` and `Liedd(a, b)` all describe the element $\mathbf{d}_{a,b}$, but regarded as an element of `DD`, $L_0$ and $L$, respectively. `dd` is a shorthand for `Liedd`. Similarly, `L0Xi` and `L0Zeta` represent $\xi$ and $\zeta$ regarded as elements of $L_0$. The functions `DDToL0Emb` and `DDToLieEmb` describe the embeddings defined on `DD`.

Since the sum of `DD` and $k \xi + k \zeta$ is not necessarily direct, there are no projection maps from $L$ (or $L_0$) onto `DD`, $k\xi$ and $k\zeta$. Still, every element `l0` of `L0` is internally represented as a sum `d + t*L0Xi + s*L0Zeta` where `d` is in `DD` and `t, s` are in $k$, and we define functions `L0DDPart(l0) := d`, `L0XiPart(l0) := t`, `L0ZetaPart(l0) := s`.

#### Root homomorphisms

We represent a root in $G_2$ (respectively, $F_4$) as a list with two (respectively, four) elements, each of which is in `[-2, -1, 0, 1, 2]`. This representation corresponds precisely to Figure ??? in \[DMW\]. For a root `a` in $F_4$, `F4RootG2Coord(a)` is its image in $G_2 \cup \{0\}$. The sets of all roots in $F_4$ and $G_2$ are stored in the lists `F4Roots` and `G2Roots`, respectively.

For a root `alpha` in $F_4$ and an element `a` of $k$ or $C$, `LieRootHomF4(alpha, a)` is the element $\vartheta_\alpha(a)$ of $L$ (see \[DMW\]). It is required that either `alpha` is short and $a \in C$, or `alpha` is long and $a \in k$.

## The automorphism group

For a root `alpha` in $F_4$ and an element `a` of $k$ or $C$, `GrpRootHomF4(alpha, a)` is the automorphism $\theta_\alpha(a)$ of $L$ (see \[DMW\]). It is required that either `alpha` is short and $a \in C$, or `alpha` is long and $a \in k$. Further, `GrpStandardWeylF4(alpha)` is the Weyl element $w_\alpha$.

The automorphisms defined above lie in the internal structure `LieEndo`. For an element `f` of `LieEndo` and `lie` in $L$, `f` may be evaluated on `lie` in the usual way, by writing `f(lie)`. For two elements `f` and `g` of `LieEndo`, `f+g` and `f*g` are the elements of `LieEndo` that map `lie` to `f(lie) + g(lie)` and `f(g(lie))`, respectively.

## Trivial elements

The zero elements in $k$, $C$, $B$, `DD`, $L_0$, $L$, `LieEndo` may be accessed as `Zero(ComRing)`, `Zero(ConicAlg)`, `BrownZero`, `DDZero`, `L0Zero`, `LieZero` and `GrpZero`. The identity element of `LieEndo` may be accessed as `GrpOne`.

## Simplification

Let `a` be an element of $C$. Then `Simplify(a)` represents the same element of (the free multiplicative conic alternative algebra `C`), but its internal representation is (hopefully) simplified. In many situations, if `a` represents the zero element in $C$, then the internal representation of `Simplify(a)` is trivial. Thus in order to check whether `a = b`, one should always check whether `Simplify(a-b) = Zero(ConicAlg)`: If this is true, then `a` and `b` are proven to represent the same element of $C$. However, if it is `false`, this does not prove that they represent distinct elements.

The function `Simplify` is also defined on $k$, $B$, `DD`, $L_0$ and $L$, and works on these structures in a similar way. For more details, we refer to Section 9.3 (TODO: number still correct?) in \[DMW\].

## Testing equality of automorphism of $L$

Let `g, h` be elements of `LieEndo` which are assumed to be compatible with the Lie bracket. We can try to prove that `g` equals `h` by checking that `Simplify(g(gen) - h(gen))` is zero (in $L$) for all `gen` in a set of Lie algebra generators of $L$. Two functions are available for this task:
- `TestEquality(g, h)` is `true` if all checks described above are successful. Otherwise it is the list of all lists `[gen, Simplify(g(gen) - h(gen))]` for any `gen` for which the test was not successfull.
- `TestEqualityPieces(g, h)` is `true` if all checks described above are successful. Otherwise it is a list of all non-zero elements of $k$, $C$ and $L_0$ that appear in `Simplify(g(gen) - h(gen))` for any `gen`.

The general strategy for proving equality of `g` and `h` is to call `TestEqualityPieces(g, h)` and to prove by hand that all terms in the result (if there are any) equal zero.

The list of all generators `gen` on which we test equality is obtained by evaluating all root homomorphisms with image in $L_{-2} + L_1$ on the last indeterminate in $k$ or $C$ (that is, on `ComRingIndet(ComRing_rank)` or `ConicAlgIndet(ConicAlg_rank)`). The user should assure that these indeterminates do not occur in `g` and `h`.

# License

This software is licensed under the GPL-3.0 license.
