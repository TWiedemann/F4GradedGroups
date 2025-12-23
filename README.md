# Introduction

This [GAP](https://www.gap-system.org/) package allows basic symbolic computation in free multiplicative conic alternative algebras (over free commutative rings, that is, polynomial rings).
In other words, it provides a framework to prove that certain identities hold in any multiplicative conic alternative algebra over any commutative ring by deriving these identities from a set of known identities in such objects.
It also supports similar computations in the Lie algebra and the group of automorphisms that are constructed in the preprint \[DMW\] *Cubic norm pairs and $G_2$- and $F_4$-graded groups and Lie algebras* (TODO: arXiv link) from an arbitrary multiplicative conic alternative algebra.
It cannot prove any such identity (which seems to be a hopeless task), but it is powerful enough to prove all identities that are needed in \[DMW\].
The basic strategy of this implementation is described in \[DMW, 9.3\].

# Installation

1. Install the latest version of [GAP](https://www.gap-system.org/install/). This package requires GAP version at least 4.15.0, and has been tested with GAP version 4.15.1. It will run into errors with GAP version 4.14.0 or lower.
2. Download (via the green "Code" button on GitHub, or using `git clone`) this repository into a new directory `[gap]/pkg/F4GradedGroups` inside your `gap` directory. Thus the `init` file of this package should lie in `[gap]/pkg/F4GradedGroups/init.g`. On Windows, the path `[gap]` might be something like TODO, depending on where you installed GAP.

# Using this package

1. In GAP, load the package with `LoadPackage("F4GradedGroups");`.
2. Initialise the package with `InitF4Graded();`.

For details, see [`doc/manual.md`](https://github.com/TWiedemann/F4GradedGroups/blob/main/doc/manual.md). Usage examples may also be found in (the text file) `tst/test_basic.tst`.

# Verification of the claims in \[DMW\]

For each of the files in `[gap]/pkg/F4GradedGroups/tst`, do the following to perform the tests in this file that verify the claims in \[DMW\].
1. Start a GAP session.
2. Type `LoadPackage("F4GradedGroups");` and press Enter to load the package. Do NOT call `InitF4Graded()`, this will be done automatically by the following steps.
3. Type `Test("filepath", rec(width:=50000));` and press Enter. Here `filepath` should be replaced by the path of the file you want to test. On Unix, if you started the GAP session inside `[gap]/pkg/F4GradedGroups/tst`, then `filepath` can simply be the name of the file, e.g. `Test("test_basic.tst", rec(width:=50000));`. On Windows, it could be something like TODO.
4. An output of `true` on the terminal signifies that all tests were successful. Some tests run only a few seconds, others may take 10 minutes or longer.
5. To test the next file, close GAP and start a new session.

Specifically, the files perform the following tests:
- `test_basic.tst` does not verify any specific claim in \[DMW\]. Rather, it tests that all basic functions of the package work as intended.
- `test_jordan_brace.tst` verifies \[DMW, 9.15\] (explicit formulas for the $D$-operators in cubic Jordan matrix algebras).
- `test_lie_comm.tst` verifies \[DMW, 10.32, 10.33, 10.34\] (existence of a Chevalley-type basis and explicit commutator formulas in the Lie algebra).
- `test_group_comm.tst` verifies \[DMW, 11.12\] (commutator formulas in the $F_4$-graded group).
- `test_weyl.tst` verifies \[DMW, 11.5, 11.11\] (the elements $w_\delta$ are Weyl elements with the desired parities).

The last two test files require a few more computations by hand to complete the proof of the specified claims. See the comments of the respective test files for details.

# License

This software is licensed under the GPL-3.0 license.
