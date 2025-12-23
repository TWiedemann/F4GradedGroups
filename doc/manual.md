# Initialisation

This package allows symbolic computations in a free multiplicative conic alternative algebra $C$ on generators `a1, a2, ...` over a free commutative ring $k$ on generators `t1, t2, ...`. For technical reasons, three constants that must be set during initialisation limit the ring elements that may arise during runtime:
- `ComRing_rank` is the number of *indeterminates* `t1, t2, ...`. If for example `ComRing_rank = 3`, then `t1, t2, t3` are defined but `t4` is not.
- `ConicAlg_rank` is the number of *indeterminates* `a1, a2, ...`.
- `Trace_MaxLength` is the maximal length of products that may appear inside the argument of the trace function of $C$. For example, if `Trace_MaxLength = 2`, then `tr(a1a2)` is defined but  `tr(a1a2a1)` is not.

These constants may be set by the user with the following function (after loading the package with `LoadPackage("F4GradedGroups")`):

```
InitF4Graded(comrank, conicrank, tracelength, userVars)
```
Initialises the package with `ComRing_rank := comrank`, `ConicAlg_rank := conicrank`, `Trace_MaxLength := tracelength`. If `userVars = true`, then the following GAP variables are defined for the user's convenience: `t1, t2, ...` for the generators of $k$; `a1, a2, ...` for the generators of $C$; `g1, g2, g3` for the (arbitrary) constants $\gamma_1, \gamma_2, \gamma_3$ in $k$ (see below); `dd` for `Liedd` (see below). If `userVars = false`, then for example the indeterminates in $k$ are still printed as `t1, t2, ...`, but no GAP variables of the same name are defined to easily access these elements of $k$.

High values of `ConicAlg_rank` and `Trace_MaxLength` strongly impact the runtime of computations. All serious computations needed in \[DMW\] work in the setup `InitF4Graded(6, 3, 4, false)` or `InitF4Graded(6, 2, 4, false)`.

# Notational conventions

In the following, we denote elements of $k$ by `t, s, r`, elements of $C$ by `a, b, c`, elements of the cubic Jordan matrix algebra by `cub`, elements of the Brown algebra $B$ by `brown`, elements of `DD` by `ddEl`, elements of $L_0$ by `l0`, elements of $L$ by `lie` and elements of `LieEndo` by `f, g`. Further, we denote by `i, j, l` integers in ˙[1,2,3]˙ and by `p` arbitrary integers.

# The commutative ring $k$

Internally, we use the name `ComRing` for the commutative ring $k$.

```
ComRingIndet(i)
```
Returns the `i`-th indeterminate in $k$, which is printed as `ti`. If the package was initialised with `userVars = true`, then GAP variables `t1 := ComRingIndet(1), ...` are defined.

```
ComRingGamIndet(i)
```
Returns the `i`-th element of $\Gamma = (\gamma_1, \gamma_2, \gamma_3)$. These are the (arbitrarily chosen, but fixed) constants that appear in the definition of cubic Jordan matrix algebras. They are printed as `g1, g2, g3`. If the package was initialised with `userVars = true`, then GAP variables `g1 := ComRingGamIndet(1), ...` are defined.

```
+, *, ^-1
```
The usual arithmetic operations in GAP for addition, multiplication and inversion are available for elements of $k$.

# The multiplicative conic alternative algebra $C$

Internally, we use the name `ConicAlg` for the multiplicative conic alternative $k$-algebra $C$.

```
ConicAlgIndet(i)
```
Returns the `i`-th indeterminate in $C$, which is printed as `ai`. If the package was initialised with `userVars = true`, then GAP variables `a1 := ConicAlgIndet(1), ...` are available.

```
+, *, ^-1
```
The usual arithmetic operations in GAP for addition and multiplication (but not inversion) are available for elements of $k$.

```
ConicInv(a)
```
Returns the conjugate of `a`. This is an element of $C$ which is printed as `a'`.
```
ConicNorm(a)
```
Returns the norm of `a`. This is an element of $k$ which is printed as `n(a)`.
```
ConicTr(a)
```
Returns the trace of `a`. This is an element of $k$ which is printed as `tr(a)`.

Several measures are taken to simplify (the display of) traces.
Multiplication signs in the argument of the trace are not printed:
For `a=a1*a2`, the trace of `a` is printed as `tr(a1a2)`.
By the relation `tr((ab)c) = tr(a(bc))`, we can omit brackets in products of length at most 3, so the result of `ConicTr((a1*a2)*a3)` is printed as `tr(a1a2a3)`.
Using in addition the relations `tr(a') = tr(a)` and `tr(ab) = tr(ba)`, the arguments of the trace are often permuted and/or replaced by their conjugates to ensure proper cancellation of terms.
For example, both `ConicTr(a1*ConicInv(a2))` and `ConicTr(ConicInv(a1)*a2)` evaluate to `tr(a1a2')`, and `ConicTr(ConicInv(a1)*a2*a3)` evaluates to `tr(a1a3'a2')` (which is correct because `tr(a1'a2a3) = tr((a1'a2a3)') = tr(a3'a2'a1) = tr(a1a3'a2')`).
```
ConicNormLin(a, b)
```
Returns `n(a+b)-n(a)-n(b)`, which is known to be the same as `tr(a'b)`.



# The cubic Jordan matrix algebra

Internally, we use the name `Cubic` for the cubic Jordan matrix algebra $J \coloneqq\operatorname{Her}_3(C, \Gamma)$.

## Elements of the cubic Jordan matrix algebra

```
CubicConicEl(a, i)
```
Returns `a[jl]` where `[i,j,l]` is the unique cyclic permutation of `[1,2,3]` starting from `i`.
```
CubicComEl(t, i)
```
Returns the element of $J$ which is denoted by $te_i$ in \[DMW\]. It is printed as `t[ii]`.
```
CubicElMat(z, i, j)
```
Returns `z[ij]`. Thus `z` must lie in $k$ if `i=j` and in $C$ otherwise.
```
CubicElFromTuple(t, s, r, a, b, c)
```
Returns  `t[11] + s[22] + r[33] + a[23] + b[31] + c[12]`.
```
CubicConicPart(cub, i)
CubicComPart(cub, i)
```
Returns the corresponding component of `cub`. For example, for `cub = t[11] + s[22] + r[33] + a[23] + b[31] + c[12]`, we have `CubicConicPart(cub, 1) = a` and `CubicComPart(cub, 2) = s`.
```
+, *
```
The usual GAP operations for addition $+: J \times J \to J$ and scalar multiplication $\cdot: k \times J \to J$ are available on $J$.

## The cubic norm structure

$J$ has the structure of a cubic norm structure, whose structural maps can be computed as follows.
```
CubicNorm(cub)
```
Returns the norm of `cub`, which is an element of $k$.
```
CubicAdj(cub)
```
Returns the adjoint $\text{cub}^\sharp$ of `cub`, which is an element of $J$.
```
CubicBiTr(cub1, cub2)
```
Returns the bilinear trace $T(\text{cub1}, \text{cub2})$ of `cub1`, `cub2`, which is an element of $k$.
```
CubicCross(cub1, cub2)
```
Returns $\text{cub1} \times \text{cub2}$, which is an element of $J$.

## The Jordan algebra structure

$J$ has the structure of a quadratic Jordan algebra, whose structural maps can be computed as follows.
```
JordanU(cub1, cub2)
```
Returns $U_{\text{cub1}}(\text{cub2})$, which is an element of $J$.
```
JordanULin(cub1, cub2, cub3)
```
Returns $U_{\text{cub1},\text{cub2}}(\text{cub3})=U_{\text{cub1}+\text{cub2}}(\text{cub3}) - U_{\text{cub1}}(\text{cub3}) - U_{\text{cub2}}(\text{cub3})$, which is an element of $J$.
```
JordanD(cub1, cub2, cub3)
```
Returns $D_{\text{cub1}, \text{cub2}}(\text{cub3}) = \{\text{cub1}, \text{cub2}, \text{cub3}\} = U_{\text{cub1}, \text{cub3}}(\text{cub2})$, which is an element of $J$.

# The Brown algebra

We refer to the $k$-module $B = (k, J, J', k)$ as the *Brown algebra* because, if $2$ is invertible in $k$, then it has the structure of a structurable algebra that is known under this name.
It parametrises the $1$- and $(-1)$-parts of the Lie algebra that we construct in \[DMW\].

Note that while elements of $B$ are internally represented and also printed as lists `[t, cub1, cub2, s]`, they are not lists in the GAP sense. Thus for an element `brown` of $B$, we have `IsList(brown) = false` and `brown[1]` is not a well-defined expression.
```
BrownElFromTuple(t, cub1, cub2, s)
```
Returns the element `[ t, cub1, cub2, s ]` of $B$. 
```
BrownElTuple(brown)
```
Returns the GAP list `[ t, cub1, cub2, s ]` underlying `brown`.
```
BrownElPart(brown, p)
```
Returns the `p`-th entry of the list underlying `brown`, where `1 <= p <= 4`.
```
BrownElComPart(brown, p)
```
Returns `BrownElPart(brown, 1)` for `p=1` and `BrownElPart(brown, 4)` for `p=2`.
```
BrownElCubicPart(brown, p)
```
Returns `BrownElPart(brown, 2)` for `p=1` and `BrownElPart(brown, 3)` for `p=2`.

# The Lie algebra

The Lie algebra $L$ that we construct from $J$ is, as a $k$-module, a direct sum $\bigoplus_{i=-2}^2 L_i$. We refer to it as `Lie` in the documentation and in our naming conventions.

```
LiePart(lie, p)
```
Returns the projection of `lie` to $L_p$ where `-2 <= p <= 2`. This is an element of $k$ if $p = \pm 2$, and element of $B$ if $p = \pm 1$ and an element of $L_0$ if $p=0$.
```
+, *
```
As usual in GAP, the sum and Lie bracket of two elements of $L$ can be computed as `lie1 + lie2` and `lie1 * lie2`, respectively. Further, the scalar multiplication $k \times L \to L$ can also be computed using `*`.

## The parts $L_{-2}$ and $L_2$

The $k$-submodules $L_{-2}$ and $L_2$ are isomorphic to $k$.

```
LieX, LieY
```
The generators of $L_{-2}$ and $L_2$, respectively. They are denoted by $x$ and $y$ in \[DMW\]. They are printed as `x` and `y`.

## The parts $L_{-1}$ and $L_1$

The $k$-submodules $L_{-1}$ and $L_1$ are isomorphic to the Brown algebra $B$. However, just like elements of $B$ are not lists in the GAP sense, we strictly distinguish between elements of $B$, $L_{-1}$ and $L_1$. Elements of $L_{-1}$ and $L_1$ are printed as `[t, cub1, cub2, s]_-` and `[t, cub1, cub2, s]_+`, respectively. For example, `[ t1, a1[23], a2[12], t1+t2 ]_+` is an element of $L_1$.

```
BrownPosToLieEmb(brown)
BrownNegToLieEmb(brown)
```
Returns the element `brown_+` of $L_1$ or `brown_-` of $L_{-1}$, respectively.
```
LieBrownPosElFromTuple(t, cub1, cub2, s)
LieBrownNegElFromTuple(t, cub1, cub2, s)
```
Returns the element `[t, cub1, cub2, s]_+` of $L_1$ or `[t, cub1, cub2, s]_-` of $L_{-1}$, respectively.

## The Lie subalgebra $L_0$

The subalgebra $L_0$ of $L$ is itself the direct sum of three components $L_{0,-1}, Z, L_{0,1}$. Again, we internally distinguish between elements of $L_0$ and their embedding into $L$.
```
L0ToLieEmb(l0)
```
Returns the embedding of `l0` into $L$.

### The parts $L_{0,-1}$ and $L_{0,1}$

The $k$-submodules $L_{0,-1}$ and $L_{0,1}$ are isomorphic to the cubic Jordan matrix algebra $J$. Again, we strictly distinguish between elements of $J$, $L_{0,-1}$ and $L_{0,1}$. For an element `cub` of $J$, the corresponding elements of $L_{0,-1}$ and $L_{0,1}$ are printed as `ad_{cub}^-` and `ad_{cub}^+`, respectively. While we internally distinguish between elements of $L_{0,\pm 1}$ and their embeddings into $L$, they are printed in the same way.

```
CubicPosToL0Emb(cub)
CubicNegToL0Emb(cub)
```
Returns the elements `ad_{cub}^+` and `ad_{cub}^-` of $L_0$, respectively.
```
CubicPosToLieEmb(cub)
CubicNegToLieEmb(cub)
```
Returns the elements `ad_{cub}^+` and `ad_{cub}^-` of $L$, respectively.
```
L0CubicPosPart(l0)
L0CubicNegPart(l0)
```
Returns the projection of `l0` onto $L_{0,1}$ or $L_{0,-1}$, respectively.

### The parts $Z$ and `DD`

We refer to the $k$-module $\langle \mathbf{d}_{a,b} \mid a \in J, b \in J' \rangle$ (which is unnamed in \[DMW\]) as `DD` in (the documentation of) this GAP package. The $k$-module $Z$ is the (not necessarily direct) sum of `DD` with $k \xi + k\zeta$. Again, we internally distinguish between elements of `DD` and their embedding into $L_0$ and $L$.
```
LieXi
L0Xi
LieZeta
L0Zeta
```
The elements $\xi$ and $\zeta$ regarded as elements of $L$ or of $L_0$, respectively. They are printed as `xi` and `zeta`.
```
DDdd(cub1, cub2)
L0dd(cub1, cub2)
Liedd(cub1, cub2)
```
Returns the element $\mathbf{d}_{\text{cub1},\text{cub2}}$, regarded as an element of `DD`, $L_0$ or $L$, respectively. In all three cases, it is printed as `dd_{cub1,cub2}`. If the package was initialised with `userVars = true`, then the shortcut `dd := Liedd` is defined.
```
DDToL0Emb(ddEl)
DDToLieEmb(ddEl)
```
Returns the embedding of `ddEl` into $L_0$ or $L$, respectively.
```
L0DDPart(l0)
L0XiPart(l0)
L0ZetaPart(l0)
```
Returns elements of `DD` and $k$ such that the projection of `l0` onto $Z$ is `L0DDPart(l0) + L0XiPart(l0)*L0Xi + L0ZetaPart(l0)*L0Zeta`. Note that since the sum of `DD` and $k \xi + k \zeta$ is not necessarily direct, these elements are not uniquely determined by this property.

## Root homomorphisms

We represent a root in $G_2$ (respectively, $F_4$) as a list with two (respectively, four) elements, each of which is an integer in the range `[-2, -1, 0, 1, 2]`. This representation corresponds precisely to Figures 1 and 3 in \[DMW\].
```
F4Roots
F4ShortRoots
F4LongRoots
G2Roots
G2ShortRoots
G2LongRoots
```
Lists of all (resp. all short reps. all long) roots in $F_4$ (resp. $G_2$).
```
F4SimpleRoots
```
The system `[[1,1,-1,-1], [-2, 0, 0, 0], [1, -1, 0, 0], [0, 1, 1, 0]` of simple roots in $F_4$. This is precisely $\Delta_F = (\delta_1, \delta_2, \delta_3, \delta_4)$ in \[DMW, 11.1\].
```
F4RootG2Coord(F4Root)
```
Returns the image of `F4Root` under the surjection $\pi: F_4 \to G_2 \cup \{0\}$ described in \[DMW, 10.24\].
```
F4Refl(F4Root1, F4Root2)
```
Returns $\text{F4Root1}^{\sigma(\text{F4Root2})}$, the image of `F4Root1` along the hyperplane orthogonal to `F4Root2`.
```
LieRootHomF4(F4Root, z)
```
Returns the element $\vartheta_\alpha(z)$ of $L$ as defined in \[DMW, 10.29\]. Thus `z` must be in $k$ if `F4Root` is long and in $C$ otherwise.

# The automorphism group

The $F_4$-graded group constructed in \[DMW\] is a group of automorphisms of $L$. This package provides the internal structure `LieEndo` to perform computations with automorphisms of $L$.
```
f(lie)
```
For an element `f` of `LieEndo` and `lie` in $L$, `f(lie)` is the image of `lie` under `f`.
```
f+g, f*g
```
For two elements `f` and `g` of `LieEndo`, `f+g` and `f*g` are the elements of `LieEndo` that map `lie` to `f(lie) + g(lie)` and `f(g(lie))`, respectively.
```
GrpRootHomF4(F4Root, z)
```
Returns the automorphism $\theta_\alpha(a)$ of $L$ in `LieEndo` as defined in \[DMW, 11.2, 11.8\]. Thus `z` must be in $k$ if `F4Root` is long and in $C$ otherwise.
```
GrpStandardWeylF4(F4Root)
```
Returns the Weyl element $w_\alpha = \theta_{-\alpha}(-1) \theta_\alpha(1) \theta_{-\alpha}(-1)$ in `LieEndo`.


# Trivial elements

```
Zero(ComRing)
Zero(ConicAlg)
BrownZero
DDZero
L0Zero
LieZero
GrpZero
```
The zero elements in $k$, $C$, $B$, `DD`, $L_0$, $L$, `LieEndo`, respectively.
```
GrpOne
```
The identity element in `LieEndo`.

# Simplification and equality tests

Let `u, v` be two element of $k$ (or of $C$, $B$, `DD`, $L_0$ or $L$, but not of `LieEndo` which is handled somewhat differently). Then `u = v` evaluates to `true` if and only if the internal representations of `u` and `v` coincide. In particular, if it evaluates to `true`, then `u` and `v` are certainly equal (in the mathematical sense, i.e. regarded as elements of a "free" mathematical structure). If for example `u`, `v` lies in $C$, this means that for any multiplicative conic alternative algebra $\tilde{C}$ over any commutative ring $\tilde{k}$, the identity `u = v` holds whenever `a1, a2, ...` are replaced by arbitrary elements of $\tilde{C}$ and `t1, t2, ...` are replaced by arbitrary elements of $\tilde{k}$.

However, it `u = v` evaluates to `false`, then this does not prove that `u` and `v` are not equal (in the mathematical sense). The following key function of this package aims to mitigate this problem:

```
Simplify(u)
```
Returns an element of the parent structure of `u` (that is, of $k$, $C$, $B$, `DD`, $L_0$ or $L$) which is mathematically equivalent to `u`. Usually the internal representation of `Simplify(u)` is "easier"/"shorter"/"more canonical" than that of `u`.

Thus to check whether `u = v`, one should check whether `Simplify(u-v)` equals zero. If this is true, then `u` and `v` represent the same element. If not, then they might still represent the same element, and we can try to prove this by hand by showing that `Simplify(u-v)` represents 0 (which is usually easier than showing that `u-v` represents 0).

The function `Simplify` relies on several subroutines which can be studied in detail in `gap/simplify.g`. For Lie algebra elements, we also provide the following function.
```
TestEquality(lie1, lie2[, print])
```
Returns `true` if `lie1`, `lie2` can be proven to represent the same elements using the techniques outlined above, and `false` otherwise.
If the optional argument `print` is supplied and `true`, then in addition, simplifications of all non-zero components of `lie1-lie2` in $L_{-2}, \dots, L_2$ are printed.


# Testing equality of automorphism of $L$

For elements of `LieEndo`, equality tests with `=` are useless: Even `GrpRootHomF4(F4Root, z) = GrpRootHomF4(F4Root, z)` evaluates to `false` for technical reasons. Instead, the following functions should be used.
```
TestEquality(g, h)
```
Returns `true` if `TestEquality(g(gen), h(gen))` is `true` for all `gen` in a certain list of Lie algebra generators of $L$.
Otherwise returns the list of all lists `[gen, Simplify(g(gen) - h(gen))]` for any `gen` for which the test was not successfull.

The list of all generators `gen` on which we test equality is obtained by evaluating all root homomorphisms with image in $L_{-2} + L_1$ on the last indeterminate in $k$ or $C$ (that is, on `ComRingIndet(ComRing_rank)` or `ConicAlgIndet(ConicAlg_rank)`). The user should assure that these indeterminates do not occur in the definition of `g` and `h`.
```
TestEqualityPieces(g, h)
```
Returns `true` in the same situations as `TestEquality`.
Otherwise the output is a list of all non-zero "pieces" of all "error terms" `Simplify(g(gen) - h(gen))` that arise during the test.
By "pieces" we mean the underlying elements of $k$, $C$ and $L_0$ that make up the error terms.
Thus to prove that `g` and `h` are the same, it suffices to prove that all elements in the output list represent 0.

As for `TestEquality`, the user should assure that `ComRingIndet(ComRing_rank)` or `ConicAlgIndet(ConicAlg_rank)` do not occur in the definition of `g` and `h`.
