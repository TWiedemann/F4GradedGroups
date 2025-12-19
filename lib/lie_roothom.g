### This file contains the definition of the root homomorphisms,
### of the Chevalley basis and of the generators of Lie

## -------- Root homomorphisms into Cubic --------

DeclareOperation("CubicRootHomLong", [IsInt, IsRingElement, IsInt, IsBool]);
DeclareOperation("CubicRootHomLong", [IsInt, IsRingElement, IsInt]);

# l: Number in {1, 2, 3}
# a: Element of ComRing
# sign: 1 or -1
# noGamma: Bool
# naive: If true, then no multiplication by gamma occurs
# Returns: If noGamma = false (which is the default):
# - If sign=1, the image of the root homomorphism in Cubic with image J_{ll}.
# - If sign=-1, the image of the root homomorphism in Cubic' with image J_{ll}'.
# If noGamma = true, then no multiplication by g1, g2, g3 occurs, so that these are
# simply the "naive" root homomorphisms.
InstallMethod(CubicRootHomLong, [IsInt, IsRingElement, IsInt, IsBool], function(l, a, sign, noGamma)
	local i, j, lambda;
	ReqComRingEl(a);
	if not noGamma then
		i := CycPerm[l][2];
		j := CycPerm[l][3];
		lambda := ComRingGamIndet(j) * ComRingGamIndet(i)^-1;
		if sign = -1 then
			lambda := lambda^-1;
		fi;
	else
		lambda := One(ComRing);
	fi;
	return CubicComEl(l, lambda * a);
end);

# Default value: noGamma = false
InstallMethod(CubicRootHomLong, [IsInt, IsRingElement, IsInt], function(l, a, sign)
	return CubicRootHomLong(l, a, sign, false);
end);

DeclareOperation("CubicRootHomShort", [IsInt, IsRingElement, IsInt, IsBool]);
DeclareOperation("CubicRootHomShort", [IsInt, IsRingElement, IsInt]);

# l: Number in {1, 2, 3}. Denote by (i,j,l) the corresponding cyclic perm. of (1,2,3).
# a: Element of ComRing
# sign: 1 or -1
# noGamma: If true, then no multiplication by gamma occurs
# Returns: If sign=1, the image of the root homomorphism in Cubic with image J_{ij}.
# If sign=-1, the image of the root homomorphism in Cubic' with image J_{ij}'.
InstallMethod(CubicRootHomShort, [IsInt, IsRingElement, IsInt, IsBool], function(l, a, sign, noGamma)
	local i, j, lambda;
	ReqConicAlgEl(a);
	if not noGamma then
		i := CycPerm[l][2];
		j := CycPerm[l][3];
		if sign = 1 then
			lambda := ComRingGamIndet(j)^-1;
		else
			lambda := ComRingGamIndet(i)^-1;
		fi;
	else
		lambda := One(ComRing);
	fi;
	return CubicConicEl(l, lambda * a);
end);

# Default value: noGamma = false
InstallMethod(CubicRootHomShort, [IsInt, IsRingElement, IsInt], function(l, a, sign)
	return CubicRootHomShort(l, a, sign, false);
end);

## -------- Root homomorphisms into Brown algebra --------

DeclareOperation("BrownRootHom", [IsList, IsRingElement, IsBool]);
DeclareOperation("BrownRootHom", [IsList, IsRingElement]);

# subroot: List [r2, r3, r4] of integers with [1, r2, r3, r4] \in F4
# (equivalently, [-1, r2, r3, r4] \in F4).
# a: An element of ConicAlg or of Comring
# noGamma: Bool.
# Returns: If noGamma = false (default), the image of the root
# homomorphism w.r.t. [r2,r3,r4] in Brown.
# Then CubicPosToLieEmb(image) is the image of the [1,r2,r3,r4]-root homomorphism in Lie,
# and CubicNegToLieEmb(image) is the image of the [-1,r2,r3,r4]-root homomorphism in Lie.
# If noGamma = true, then no multiplication by g1, g2, g3 occurs, so that these are
# simply the "naive" root homomorphisms.
InstallMethod(BrownRootHom, [IsList, IsRingElement, IsBool], function(subroot, a, noGamma)
	local cub, l, sign;
	if not Concatenation([1], subroot) in F4Roots then
		Error("Invalid argument");
		return fail;
	fi;
	if subroot = [1,1,1] then
		return BrownElFromTuple(Zero(ComRing), CubicZero, CubicZero, a);
	elif subroot = [-1, -1, -1] then
		return BrownElFromTuple(a, CubicZero, CubicZero, Zero(ComRing));
	elif Sum(subroot) = 1 then # Root space lies in Cubic'
		l := Position(subroot, -1);
		if l <> fail then # Long root
			ReqComRingEl(a);
			cub := CubicRootHomLong(l, a, -1, noGamma);
		else # Short root
			ReqConicAlgEl(a);
			l := Position(subroot, 1);
			cub := CubicRootHomShort(l, a, -1, noGamma);
		fi;
		return BrownElFromTuple(Zero(ComRing), CubicZero, cub, Zero(ComRing));
	else # Root space lies in Cubic
		l := Position(subroot, 1);
		if l <> fail then # Long root
			ReqComRingEl(a);
			cub := CubicRootHomLong(l, a, 1, noGamma);
		else # Short root
			ReqConicAlgEl(a);
			l := Position(subroot, -1);
			cub := CubicRootHomShort(l, a, 1, noGamma);
		fi;
		return BrownElFromTuple(Zero(ComRing), cub, CubicZero, Zero(ComRing));
	fi;
end);

# Default: noGamma = false
InstallMethod(BrownRootHom, [IsList, IsRingElement], function(subroot, a)
	return BrownRootHom(subroot, a, false);
end);

## -------- Root homomorphisms in DD --------

DeclareOperation("DDRootHomA2", [IsList, IsRingElement, IsBool]);
DeclareOperation("DDRootHomA2", [IsList, IsRingElement]);

# root: A root in A_2 (e.g. [1, -1, 0]).
# a: An element of ConicAlg.
# noGamma: If true, then no multiplication by gamma occurs
# Returns: If noGamma = false (default), the image of the root homomorphism in DD.
# If noGamma = true, then no multiplication by g1, g2, g3 occurs, so that these are
# simply the "naive" root homomorphisms.
InstallMethod(DDRootHomA2, [IsList, IsRingElement, IsBool], function(root, a, noGamma)
    local i, j, l, lambda;
    ReqConicAlgEl(a);
    # The root space w.r.t. root is Z_{i \to j}
    i := Position(root, 1);
    j := Position(root, -1);
    l := Position(root, 0);
	if not noGamma then
		if root = [1, -1, 0] then
			lambda := ComRingGamIndet(1)^-1 * ComRingGamIndet(2)^-1 * ComRingGamIndet(3);
		elif root = [-1, 1, 0] then
			lambda := ComRingGamIndet(3)^-1;
		elif root = [1, 0, -1] then
			lambda := ComRingGamIndet(2)^-1;
		elif root = [-1, 0, 1] then
			lambda := ComRingGamIndet(1)^-1 * ComRingGamIndet(2) * ComRingGamIndet(3)^-1;
		elif root = [0, 1, -1] then
			lambda := ComRingGamIndet(1) * ComRingGamIndet(2)^-1 * ComRingGamIndet(3)^-1;
		elif root = [0, -1, 1] then
			lambda := ComRingGamIndet(1)^-1;
		else
			return fail;
		fi;
	else
		lambda := One(ComRing);
	fi;
    return DDdd(CubicComEl(i, One(ComRing)), lambda*CubicConicElMat(i, j, a));
end);

# Default: noGamma = false.
InstallMethod(DDRootHomA2, [IsList, IsRingElement], function(root, a)
	return DDRootHomA2(root, a, false);
end);

## -------- Root homomorphisms in Lie --------

DeclareOperation("LieRootHomF4", [IsList, IsRingElement, IsBool, IsBool]);
DeclareOperation("LieRootHomF4", [IsList, IsRingElement]);

# List of roots whose root homomorphisms get an additional minus sign
if not IsBoundGlobal("_MinusSignRootsLong") then
	_MinusSignRootsLong := Difference(
		F4NegLongRoots, 
		[ [-1, -1, -1, 1], [1, 1, -1, 1], [1, -1, 1, 1], [-1, 1, 1, 1] ]
	);
	MakeConstantGlobal("_MinusSignRootsLong");
fi;
if not IsBoundGlobal("_MinusSignRootsShort") then
	_MinusSignRootsShort := [
		[1, 0, -1, 0], [0, 1, 0, 1], [0, 0, 1, 1], [0, -1, -1, 0],
		[-1, 1, 0, 0], [-1, 0, 0, 1]
	];
	MakeConstantGlobal("_MinusSignRootsShort");
fi;

# root: Root in F4.
# a: Element of ComRing if root is long and element of ConicAlg otherwise
# noGamma, noMinus: Bool.
# Returns: If noGamma=noMinus=false (default), the image of a
# under the root homomorphism w.r.t root in Lie.
# If noGamma = true, no multiplication by g1, g2, g3 occurs.
# If noMinus = true, no multiplication by -1 occurs.
InstallMethod(LieRootHomF4, [IsList, IsRingElement, IsBool, IsBool], function(root, a, noGamma, noMinus)
	local sum, G2Root, cub, sign, l;
	if root in F4LongRoots then
		ReqComRingEl(a);
	elif root in F4ShortRoots then
		ReqConicAlgEl(a);
	else
		Error("Argument must be a root in F4");
		return fail;
	fi;

	if not noMinus and root in Union(_MinusSignRootsLong, _MinusSignRootsShort) then
		a := -a;
	fi;
	G2Root := F4RootG2Coord(root);
	# L_{-2}
	if G2Root[1] = -2 then
		return a * LieX;
	# L_{-1}
	elif G2Root[1] = -1 then
		return BrownNegToLieEmb(BrownRootHom(root{[2..4]}, a, noGamma));
	# L_0
	elif G2Root in [[0, 1], [0, -1]] then
		sign := G2Root[2];
		l := PositionProperty(root{[2..4]}, x -> AbsoluteValue(x) = 2);
		if l <> fail then
			ReqComRingEl(a);
			cub := CubicRootHomLong(l, a, sign, noGamma);
		else
			ReqConicAlgEl(a);
			l := Position(root{[2..4]}, 0);
			cub := CubicRootHomShort(l, a, sign, noGamma);
		fi;
		if sign = 1 then
			return CubicPosToLieEmb(cub);
		else
			return CubicNegToLieEmb(cub);
		fi;
	elif G2Root = [0,0] then
		return DDToLieEmb(DDRootHomA2(root{[2..4]}, a, noGamma));
	# L_1
	elif G2Root[1] = 1 then
		return BrownPosToLieEmb(BrownRootHom(root{[2..4]}, a, noGamma));
	# L_2
	elif G2Root[1] = 2 then
		return a * LieY;
	fi;
end);

InstallMethod(LieRootHomF4, [IsList, IsRingElement], function(root, a)
	return LieRootHomF4(root, a, false, false);
end);

## -------- Lists of generators of Lie --------

# comIndetNum, conicIndetNum: Numbers of the indeterminates that should be used.
# var: Bool.
# Returns: A list of generic basic elements of Lie which generate it as a Lie algebra,
# involving indeterminates t_comIndetNum, a_conicIndetNum
# If the last (boolean) input variable is true, then the generator list contains
# LieY and elements from L_{-1}. Otherwise (and by default) it contains LieX
# and elements from L_1.
DeclareOperation("LieGensAsLie", [IsInt, IsInt, IsBool]);
DeclareOperation("LieGensAsLie", [IsInt, IsInt]);

InstallMethod(LieGensAsLie, [IsInt, IsInt, IsBool],
	function(comIndetNum, conicIndetNum, var)
		local a, t, gens, root, coord;
		t := ComRingIndet(comIndetNum);
		a := ConicAlgIndet(conicIndetNum);
		if var then
			gens := [LieY];
			coord := -1;
		else
			gens := [LieX];
			coord := 1;
		fi;
		# For all roots in L_1 (or L_{-1}), add the images of the naive root homomorphisms.
		for root in Filtered(F4Roots, x -> F4RootG2Coord(x)[1] = coord) do
			if root in F4ShortRoots then
				Add(gens, LieRootHomF4(root, a, true, true));
			else
				Add(gens, LieRootHomF4(root, t, true, true));
			fi;
		od;
		return gens;
	end);

# Default: var = false.
InstallMethod(LieGensAsLie, [IsInt, IsInt], function(comIndetNum, conicIndetNum)
	return LieGensAsLie(comIndetNum, conicIndetNum, false);
end);

# comIndetNum, conicIndetNum: Numbers of the indeterminates that should be used.
# Returns: A list of elements of Lie which generate it as a module, provided that
# g1, g2, g3 are assumed to be invertible.
# Involves indeterminates t_comIndetNum, a_conicIndetNum, a_{conicIndetNum+1}.
# Uses the formulas d_{a[ij],b[jk]} = TwistDiag[j]*d_{1[ii],ab[kk]} from [DMW]
# to reduce the number of generators, which is why we have to assume that g1, g2, g3 are invertible.
LieGensAsModule := function(comIndetNum, conicIndetNum)
	local t1, a1, a2, gens, root, i, j, gen;
	t1 := ComRingIndet(comIndetNum);
	a1 := ConicAlgIndet(conicIndetNum);
	a2 := ConicAlgIndet(conicIndetNum + 1);
	gens := [LieXi, LieZeta];
	## For generators outside DD, we can simply use the naive root homomorphisms
	for root in F4Roots do
		if F4RootG2Coord(root) <> [0, 0] then
			if root in F4ShortRoots then
				Add(gens, LieRootHomF4(root, a1, true, true));
			else
				Add(gens, LieRootHomF4(root, t1, true, true));
			fi;
		fi;
	od;
	## Generators in DD
	# Generators of Z_{i \to j} for i <> j and of Z_{ii,ii}
	for i in [1..3] do
		for j in [1..3] do
			if i = j then
				gen := Liedd(CubicComEl(i, One(ComRing)), CubicComEl(i, t1));
			else
				gen := Liedd(CubicComEl(i, One(ComRing)), CubicConicElMat(i, j, a1));
			fi;
			Add(gens, gen);
		od;
	od;
	# Generators of Z_{ij,ji} for i <> j
	for i in [1..3] do
		for j in [i+1..3] do
			Add(gens, Liedd(CubicConicElMat(i, j, a1), CubicConicElMat(j, i, a2)));
		od;
	od;
	return gens;
end;
