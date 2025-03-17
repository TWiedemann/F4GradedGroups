### Cubic norm structure (i.e., cubic Jordan matrix algebra), called Cubic in the following

# We will write Cubic' for the other part of the cubic norm pair, but the structural
# maps of Cubic' are the same as those of Cubic.

TwistDiag := List([1,2,3], i -> ComRingGamIndet(i)); # [g1, g2, g3]
CycPerm := [ [1,2,3], [2,3,1], [3,1,2] ]; # List of cyclic permutations of [1,2,3]

# An element of Cubic is represented by [[x1, x2, x3], [u1, u2, u3]] where
# x1, x2, x3 lie in ComRing and u1, u2, u3 lie in ConicAlg.
# This represents the matrix
# [ [x1, g2*u3, g3*ConicAlgInv(u2)],
# 	[g1*ConicAlgInv(u3), x2, g3*u1],
#	[g1*u2, g2*ConicAlgInv(u1), x3]]
# (see [GPR24, 36.6]).

# Returns the matrix corresponding to the representation of an element of Cubic
CubicRepToMatrix := function(rep)
	local x, u, g;
	x := rep[1]; # ComRing elements
	u := rep[2]; # ConicAlg elements
	g := TwistDiag;
	return [ [x[1], g[2]*u[3], g[3]*ConicAlgInv(u[2])], [g[1]*ConicAlgInv(u[3]), x[2], g[3]*u[1]],
			[g[1]*u[2], g[2]*ConicAlgInv(u[1]), x[3]]];
end;

CubicZeroString := "0_J";

CubicRepToString := function(a)
	local stringList, i, s;
	stringList := [];
	for i in [1..3] do
		if a[1][i] <> Zero(ComRing) then
			s := Concatenation("(", String(a[1][i]), ")", "[", String(i), String(i), "]");
			Add(stringList, s);
		fi;
	od;
	for i in [1..3] do
		if a[2][i] <> Zero(ConicAlg) then
			s := Concatenation("(", String(a[2][i]), ")", "[", String(CycPerm[i][2]), String(CycPerm[i][3]), "]");
			Add(stringList, s);
		fi;
	od;
	return StringSum(stringList, CubicZeroString);
end;

CubicSpec := rec(
	ElementName := "CubicElement",
	Zero := a -> [[Zero(ComRing), Zero(ComRing), Zero(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]],
	One := a -> [[One(ComRing), One(ComRing), One(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]],
	Addition := function(a, b)
		return a+b;
	end,
	AdditiveInverse := function(a)
		return -a;
	end,
	Print := function(a)
		Print(CubicRepToString(a));
	end,
	MathInfo := IsAdditivelyCommutativeElement
);

Cubic := ArithmeticElementCreator(CubicSpec);
CubicZero := Cubic([[Zero(ComRing), Zero(ComRing), Zero(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]]);

InstallMethod(String, [IsCubicElement], x -> CubicRepToString(UnderlyingElement(x)));

# Scalar multiplication ComRing x Cubic -> Cubic (with priority 2, i.e., high enough to be used)
InstallMethod(\*, "for ComRingElement and CubicElement", [IsRingElement, IsCubicElement], 2, function(a,b)
	local rep, productRep;
	ReqComRingEl(a);
	rep := UnderlyingElement(b);
	productRep := [];
	productRep[1] := List(rep[1], x -> a*x);
	productRep[2] := List(rep[2], x -> a*x);
	return Cubic(productRep);
end);

## Getters for coefficients

# Return u_i as above
CubicElAlgCoeff := function(cubicEl, i)
	if i in [1,2,3] then
		return UnderlyingElement(cubicEl)[2][i];
	else
		Error("Cubic element: Invalid position.");
		return fail;
	fi;
end;

# Return x_i as above
CubicElComCoeff := function(cubicEl, i)
	if i in [1,2,3] then
		return UnderlyingElement(cubicEl)[1][i];
	else
		Error("Cubic element: Invalid position.");
		return fail;
	fi;
end;

# Return the matrix entry of cubicEl at position (i,j) "without TwistDiag"
CubicCoeffMat := function(cubicEl, i, j)
	local k;
	if not (i in [1,2,3] and j in [1,2,3]) then
		return fail;
	fi;
	if i = j then
		return CubicElComCoeff(cubicEl, i);
	else
		k := Difference([1,2,3], [i,j])[1]; # {1, 2, 3} = {i, j, k} as sets
		if [i, j, k] in CycPerm then
			return CubicElAlgCoeff(cubicEl, k);
		else
			return ConicAlgInv(CubicElAlgCoeff(cubicEl, k));
		fi;
	fi;
end;



## Constructors for elements of Cubic

# i: 1, 2, or 3
# t: Element of ComRing
# Output: The element x of Cubic with CubicElComCoeff(x, i) = t and every other coefficient zero.
# I.e., the element t[ii].
CubicComEl := function(i, t)
	local comList, conicList;
	ReqComRingEl(t);
	comList := [Zero(ComRing), Zero(ComRing), Zero(ComRing)];
	comList[i] := t;
	conicList := [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)];
	return Cubic([comList, conicList]);
end;

CubicComElOne := function(i)
	return CubicComEl(i, One(ComRing));
end;

# i: 1, 2, or 3
# a: Element of ConicAlg
# Output: The element x of Cubic with CubicElAlgCoeff(x, i) = a and every other coefficient zero.
# I.e., the element a[jl] if [i, j, l] is the cyclic permutation starting from i.
CubicAlgEl := function(i, a)
	local comList, conicList;
	if not ReqConicAlgEl(a) then
		return fail;
	fi;
	comList := [Zero(ComRing), Zero(ComRing), Zero(ComRing)];
	conicList := [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)];
	conicList[i] := a;
	return Cubic([comList, conicList]);
end;

# Output: a[jl]
CubicAlgElMat := function(j, l, a)
	local i;
	if not (l in [1,2,3] and j in [1,2,3] and l <> j) then
		return fail;
	else
		i := Difference([1,2,3], [j,l])[1]; # {1, 2, 3} = {i, j, l} as sets
		if [i, j, l] in CycPerm then
			return CubicAlgEl(i, a);
		else
			return CubicAlgEl(i, ConicAlgInv(a));
		fi;
	fi;
end;

CubicAlgElOne := function(i, j)
	return CubicAlgEl(i, j, One(ConicAlg));
end;

CubicEl := function(t11, t22, t33, a1, a2, a3)
	return CubicComEl(1, t11) + CubicComEl(2, t22) + CubicComEl(3, t33) + CubicAlgEl(1, a1) + CubicAlgEl(2, a2) + CubicAlgEl(3, a3);
end;

# CubicGenericElForIndets := function(i11, i22, i33, j12, j13, j23)
# 	if Maximum(i11, i22, i33) > ComRing_rank or Maximum(j12, j13, j23) > ConicAlg_rank then
# 		return fail;
# 	else
# 		return CubicEl(ComRingBasicIndet(i11), ComRingBasicIndet(i22), ComRingBasicIndet(i33), ConicAlgBasicIndet(j12), ConicAlgBasicIndet(j13), ConicAlgBasicIndet(j23));
# 	fi;
# end;

# Returns generic element with indeterminate numbers 3*i+1, 3*i+2, 3*i+3
CubicGenericEl := function(i)
	if 3*i+3 > ConicAlg_rank or 3*i+3 > ComRing_rank then
		return fail;
	else
		return CubicEl(ComRingBasicIndet(3*i+1), ComRingBasicIndet(3*i+2), ComRingBasicIndet(3*i+3), ConicAlgBasicIndet(3*i+1), ConicAlgBasicIndet(3*i+2), ConicAlgBasicIndet(3*i+3));
	fi;
end;



# A: An element of the cubic norm structure.
# Output: Zero(ComRing) if A is the zero element. Otherwise returns a non-zero coefficient of A (which lies either in ConicAlg or in ComRing).
# This will be used to determine whether an element of the Brown algebra lies in a root space.
# CubicGetNonTrivCoeff := function(A)
# 	local i, j;
# 	for i in [1..3] do
# 		for j in [i..3] do
# 			if A[i][j] <> Zero(ComRing) and A[i][j] <> Zero(ConicAlg) then
# 				return A[i][j];
# 			fi;
# 		od;
# 	od;
# 	return Zero(ComRing);
# end;

## ----- Structural maps of a cubic norm structure ------

DeclareOperation("CubicNorm", [IsCubicElement]);
DeclareOperation("CubicAdj", [IsCubicElement]);
DeclareOperation("CubicCross", [IsCubicElement, IsCubicElement]);
DeclareOperation("CubicBiTr", [IsCubicElement, IsCubicElement]);

# [GPR24, (36.4.5)]
InstallMethod(CubicNorm, [IsCubicElement], function(A)
	local sum, perm, i, j, l;
	sum := CubicElComCoeff(A, 1) * CubicElComCoeff(A, 2) * CubicElComCoeff(A, 3)
		+ TwistDiag[1] * TwistDiag[2] * TwistDiag[3] * ConicAlgTr(CubicElAlgCoeff(A, 1)*CubicElAlgCoeff(A, 2)*CubicElAlgCoeff(A, 3));
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		sum := sum - CubicElComCoeff(A, i) * TwistDiag[j] * TwistDiag[l] * ConicAlgNorm(CubicElAlgCoeff(A, i));
	od;
	return sum;
end );

# [GPR24, (36.4.4)]
InstallMethod(CubicAdj, [IsCubicElement], function(A)
	local result, perm, i, j, l, a_i, a_j, a_l, A_i, A_j, A_l, comEl, algEl;
	result := CubicZero;
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		a_i := CubicElAlgCoeff(A, i);
		a_j := CubicElAlgCoeff(A, j);
		a_l := CubicElAlgCoeff(A, l);
		A_i := CubicElComCoeff(A, i);
		A_j := CubicElComCoeff(A, j);
		A_l := CubicElComCoeff(A, l);
		comEl := A_j*A_l - TwistDiag[j]*TwistDiag[l]*ConicAlgNorm(a_i);
		result := result + CubicComEl(i, comEl);
		algEl := -A_i*a_i + TwistDiag[i] * ConicAlgInv(a_j*a_l);
		result := result + CubicAlgElMat(j, l, algEl);
	od;
	return result;
end );

# [GPR24, 36.4.6]
InstallMethod(CubicCross, [IsCubicElement, IsCubicElement], function(A, B)
	local result, perm, i, j, l, a_i, a_j, a_l, b_i, b_j, b_l, A_i, A_j, A_l, B_i, B_j, B_l, comEl, algEl;
	result := CubicZero;
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		a_i := CubicElAlgCoeff(A, i);
		a_j := CubicElAlgCoeff(A, j);
		a_l := CubicElAlgCoeff(A, l);
		b_i := CubicElAlgCoeff(B, i);
		b_j := CubicElAlgCoeff(B, j);
		b_l := CubicElAlgCoeff(B, l);
		A_i := CubicElComCoeff(A, i);
		A_j := CubicElComCoeff(A, j);
		A_l := CubicElComCoeff(A, l);
		B_i := CubicElComCoeff(B, i);
		B_j := CubicElComCoeff(B, j);
		B_l := CubicElComCoeff(B, l);
		comEl := A_j*B_l + B_j*A_l - TwistDiag[j]*TwistDiag[l]*ConicAlgNormLin(a_i, b_i);
		result := result + CubicComEl(i, comEl);
		algEl := -A_i*b_i - B_i*a_i + TwistDiag[i]*ConicAlgInv(a_j*b_l + b_j*a_l);
		result := result + CubicAlgElMat(j, l, algEl);
	od;
	return result;
end );

# [GRP24, (36.4.7)]
InstallMethod(CubicBiTr, [IsCubicElement, IsCubicElement], function(A, B)
	local result, i, j, l, perm;
	result := Zero(ComRing);
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		result := result + CubicElComCoeff(A, i)*CubicElComCoeff(B, i) + TwistDiag[j]*TwistDiag[l] * ConicAlgNormLin(CubicElAlgCoeff(A, i), CubicElAlgCoeff(B, i));
	od;
	return result;
end );

## ------- Structural maps of the corresponding Jordan algebra ----

DeclareOperation("JordanU", [IsCubicElement, IsCubicElement]);
DeclareOperation("JordanULin", [IsCubicElement, IsCubicElement, IsCubicElement]);
DeclareOperation("JordanD", [IsCubicElement, IsCubicElement, IsCubicElement]);

# Cubic x Cubic' -> Cubic
InstallMethod(JordanU, [IsCubicElement, IsCubicElement], function(a, b)
	return CubicBiTr(a,b)*a -CubicCross(CubicAdj(a), b);
end );

# Cubic x Cubic x Cubic' -> Cubic
InstallMethod(JordanULin, [IsCubicElement, IsCubicElement, IsCubicElement], function(a,b,c)
	return CubicBiTr(a, c)*b + CubicBiTr(b, c)*a - CubicCross(CubicCross(a,b), c);
end );

# Cubic x Cubic' x Cubic -> Cubic
InstallMethod(JordanD, [IsCubicElement, IsCubicElement, IsCubicElement], function(a,b,c)
	return JordanULin(a,c,b);
end );
