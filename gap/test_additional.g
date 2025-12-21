### This file contains tests of (special cases of) statements that are proven
### abstractly or by hand in [DMW].

# Tests whether GrpRootHomF4(root, _) is a homomorphism.
# If root is short: Uses indeterminates a_1, a_2, a_(ConicAlg_rank), t_(ComRing_rank),
# and it is assumed that ConicAlg_rank > 2.
# If root is long: Uses indeterminates t_1, t_2, t_(ComRing_rank), a_(ConicAlg_rank),
# and it is assumed that ComRing_rank > 2.
TestGrpRootHom := function(root)
	local x1, x2, g1, g2, g3;
	if root in F4ShortRoots then
		x1 := ConicAlgIndet(1);
		x2 := ConicAlgIndet(2);
	elif root in F4LongRoots then
		x1 := ComRingIndet(1);
		x2 := ComRingIndet(2);
	else
		return fail;
	fi;
	g1 := GrpRootHomF4(root, x1);
	g2 := GrpRootHomF4(root, x2);
	g3 := GrpRootHomF4(root, x1+x2);
	if TestEqualityPieces(g1*g2, g3) = true then
		return true;
	else
		return false;
	fi;
end;

# Tests whether GrpRootHomF4 is a homomorphism for all roots.
# Uses indeterminates a_1, a_2, t_1, t_2, a_(ConicAlg_rank), t_(ComRing_rank),
# and it is assumed that ComRing_rank > 2 and ConicAlg_rank > 2.
TestGrpRootHoms := function()
	local root;
	for root in F4Roots do
		if not TestGrpRootHom(root) then
			return false;
		fi;
	od;
	return true;
end;

# Returns: true if GrpRootHomF4NonDiv and GrpRootHomF4Div coincide on root, otherwise
# the corresponding error list of terms that have to be checked by hand.
# Uses indeterminates a_1, a_{ConicAlg_rank-1}, a_{ConicAlg_rank}, t_1, t_{ComRing_rank}
TestGrpRootHomExp := function(root)
	local a;
	if root in F4ShortRoots then
		a := ConicAlgIndet(1);
	elif root in F4LongRoots then
		a := ComRingIndet(1);
	fi;
	return TestEqualityOnModuleGens(GrpRootHomF4Div(root, a), GrpRootHomF4NonDiv(root, a));
end;

# Returns: true if TestGrpRootHomExp succeeds for all roots in F4, otherwise the error list
# for the first root for which the test does not succeed.
TestAllGrpRootHomExp := function()
	local root, test;
	for root in F4Roots do
		if F4RootG2Coord(root) <> [0,0] then
			test := TestGrpRootHomExp(root);
			if test <> true then
				Print("Problem for ", root, "\n");
				return test;
			fi;
		fi;
	od;
	return true;
end;

# Displays the test results for some of the conjugation formulas for Weyl elements in the G2-grading.
# We test these formulas only for cubic Jordan matrix algebras, so these tests do not provide a
# proof of the more general statements in [DMW]. They are merely a sanity check.
TestG2WeylFormulas := function()
	local bCub, bCubInv, bLie, bInvLie, phiMid, phiMidInv, phiR, phiRInv, phibs, phibsInv, t, iota,
		iotainv, testList, aCub, aLie1, aLie2, list, t1, a1;
	t1 := ComRingIndet(1);
	a1 := ConicAlgIndet(1);
	# Define phibs as w(bLie), a product of exponential automorphisms
	bCub := t1*CubicComEl(1,t1) + CubicComEl(2, One(ComRing)) + CubicComEl(3, One(ComRing));
	bCubInv := CubicNorm(bCub)^-1 * CubicAdj(bCub);
	bLie := LieBrownNegElFromTuple(Zero(ComRing), bCub, CubicZero, Zero(ComRing));
	bInvLie := LieBrownPosElFromTuple(Zero(ComRing), CubicZero, -bCubInv, Zero(ComRing));
	phiMid := F4Exp(-bLie);
	phiMidInv := F4Exp(bLie);
	phiR := F4Exp(-bInvLie);
	phiRInv := F4Exp(bInvLie);
	phibs := phiR * phiMid * phiR; # = \phibs^-1
	phibsInv := phiRInv * phiMidInv * phiRInv;
	# Further constants
	t := CubicNorm(bCub);
	iota := x -> t*JordanU(bCubInv, x);
	iotainv := x -> t^-1 * JordanU(bCub, x);
	# testList will contain lists [e1, e2] for which we test that phibsInv*e1*phibs=e2
	testList := [];
	# e_{(0,a,0,0)_+}^\phibs = e_{-a^\iota}
	aCub := CubicConicEl(1, a1);
	aLie1 := LieBrownPosElFromTuple(Zero(ComRing), aCub, CubicZero, Zero(ComRing));
	aLie2 := CubicNegToLieEmb(-iota(aCub));
	Add(testList, [F4Exp(aLie1), F4Exp(aLie2)]);
	# e_{(0,0,a',0)_+}^\phibs = e_{(0,-t(a')^\iota, 0, 0)_-}
	aLie1 := LieBrownPosElFromTuple(Zero(ComRing), CubicZero, aCub, Zero(ComRing));
	aLie2 := LieBrownNegElFromTuple(Zero(ComRing), -t*iotainv(aCub), CubicZero, Zero(ComRing));
	Add(testList, [F4Exp(aLie1), F4Exp(aLie2)]);
	# e_{(0,a,0,0)_-}^\phibs = e_{(0,0, -t^{-1} a^\iota, 0)_+}
	aLie1 := LieBrownNegElFromTuple(Zero(ComRing), aCub, CubicZero, Zero(ComRing));
	aLie2 := LieBrownPosElFromTuple(Zero(ComRing), CubicZero, -t^-1*iota(aCub), Zero(ComRing));
	Add(testList, [F4Exp(aLie1), F4Exp(aLie2)]);
	# Perform actual tests
	for list in testList do
		Display(TestEquality(phibsInv*list[1]*phibs, list[2]));
	od;
end;
