### This file contains the definition of the cubic Jordan matrix algebra over
### ConicAlg and ComRing with respec to the structural constants
### TwistDiag := [g1, g2, g3].
### We refer to this cubic Jordan matrix algebra as Cubic in the following.
### Cubic is a cubic norm structure and hence (Cubic, Cubic') is a cubic norm pair
### where Cubic' is a copy of Cubic. We do not distuingish between Cubic and Cubic'
### in the code, but we sometimes do in the comments and documentation.

### Internal representation:
# An element of Cubic is of the form
# x1[11]+x2[22]+x3[33] + u1[23]+u2[31]+u3[12]
# where x1, x2, x3 lie in ComRing and u1, u2, u3 lie in ConicAlg.
# x[ii] is what is called x*e_i in [DMW].
# For any cyclic permutation ijl of 123, we also put x[ji] := x'[ij].
# We internally represent this element as a list [[x1, x2, x3], [u1, u2, u3]].
# It can be thought to represent the matrix
# [ [x1, g2*u3, g3*ConicAlgInv(u2)],
# 	[g1*ConicAlgInv(u3), x2, g3*u1],
#	[g1*u2, g2*ConicAlgInv(u1), x3]]
# (see [GPR24, 36.6]).

# ----- Definition and internal representation -----

BindGlobal("TwistDiag", List([1,2,3], i -> ComRingGamIndet(i))); # [g1, g2, g3]
BindGlobal("CycPerm", [ [1,2,3], [2,3,1], [3,1,2] ]); # List of cyclic permutations of [1,2,3]

# String used to display the zero element of Cubic in the terminal
BindGlobal("_CubicZeroString", "0_J");

# a: Internal rep of an element of Cubic, as described above.
# Returns: A string to display the corresponding element of Cubic.
BindGlobal("CubicRepToString", function(a)
	local stringList, i, s;
	# Collect all summands in a list, and add "+" later
	stringList := [];
	# Display elements of ComRing.
	for i in [1..3] do
		if a[1][i] <> Zero(ComRing) then
			s := Concatenation("(", String(a[1][i]), ")", "[", String(i), String(i), "]");
			Add(stringList, s);
		fi;
	od;
	# Display elements of ConicAlg.
	for i in [1..3] do
		if a[2][i] <> Zero(ConicAlg) then
			s := Concatenation("(", String(a[2][i]), ")", "[", String(CycPerm[i][2]), String(CycPerm[i][3]), "]");
			Add(stringList, s);
		fi;
	od;
	return StringSum(stringList, "+", _CubicZeroString);
end);

# We define Cubic using the GAP function ArithmeticElementCreator

BindGlobal("CubicSpec", rec(
	ElementName := "CubicElement",
	Zero := a -> [[Zero(ComRing), Zero(ComRing), Zero(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]],
	One := a -> [[One(ComRing), One(ComRing), One(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]],
	# The representations of elements behave under "+" and "-" exactly as they should
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
));

BindGlobal("Cubic", ArithmeticElementCreator(CubicSpec));

InstallMethod(String, [IsCubicElement], x -> CubicRepToString(UnderlyingElement(x)));

# Scalar multiplication ComRing x Cubic -> Cubic (with priority 2, i.e., high enough to be used)
InstallMethod(\*, "for ComRingElement and CubicElement", [IsRingElement, IsCubicElement], 2, 
	function(a,b)
		local rep, productRep;
		ReqComRingEl(a);
		rep := UnderlyingElement(b);
		productRep := [];
		productRep[1] := List(rep[1], x -> a*x);
		productRep[2] := List(rep[2], x -> a*x);
		return Cubic(productRep);
end);

# ----- Getter functions for coefficients of elements of Cubic -----

# cubicEl: Element of Cubic
# i: 1, 2, or 3
# Returns: u \in Conic such that u[jl] is the jl-summand of cubicEl where ijl is
# the unique cyclic permutation starting from i
BindGlobal("CubicConicPart", function(cubicEl, i)
	if i in [1,2,3] then
		return UnderlyingElement(cubicEl)[2][i];
	else
		Error("Cubic element: Invalid position.");
		return fail;
	fi;
end);

# Returns: t \in ComRing such that t[ii] is the ii-summand of cubicEl.
BindGlobal("CubicComPart", function(cubicEl, i)
	if i in [1,2,3] then
		return UnderlyingElement(cubicEl)[1][i];
	else
		Error("Cubic element: Invalid position.");
		return fail;
	fi;
end);

# Returns: a \in ComRing or a \in ConicAlg such that a[ij] is the ij-summand of cubicEl.
DeclareGlobalName("CubicPartMat");
BindGlobal("CubicPartMat", function(cubicEl, i, j)
	if i=j then
		return CubicComPart(cubicEl, i);
	elif CycPerm[i][2] = j then
		return CubicConicPart(cubicEl, CycPerm[i][3]);
	else
		return ConicAlgInv(CubicPartMat(cubicEl, j, i));
	fi;
end);

# ----- Constructors for elements of Cubic -----

BindGlobal("CubicZero", Cubic([[Zero(ComRing), Zero(ComRing), Zero(ComRing)], [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)]]));

# TODO: Change order of arguments in CubicComEl and CubicConicEl

# i: 1, 2, or 3
# t: Element of ComRing
# Returns: The element t[ii] of Cubic.
DeclareOperation("CubicComEl", [IsRingElement, IsInt]);
InstallMethod(CubicComEl, [IsRingElement, IsInt], function(t, i)
	local comList, conicList;
	ReqComRingEl(t);
	comList := [Zero(ComRing), Zero(ComRing), Zero(ComRing)];
	comList[i] := t;
	conicList := [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)];
	return Cubic([comList, conicList]);
end);

# i: 1, 2, or 3
# Returns: The element 1[ii] of Cubic.
BindGlobal("CubicComElOne", function(i)
	return CubicComEl(One(ComRing), i);
end);

# i: 1, 2, or 3
# a: Element of ConicAlg
# Returns: The element a[jl] of Cubic if [i, j, l] is the cyclic permutation starting from i.
BindGlobal("CubicConicEl", function(a, i)
	local comList, conicList;
	if not ReqConicAlgEl(a) then
		return fail;
	fi;
	comList := [Zero(ComRing), Zero(ComRing), Zero(ComRing)];
	conicList := [Zero(ConicAlg), Zero(ConicAlg), Zero(ConicAlg)];
	conicList[i] := a;
	return Cubic([comList, conicList]);
end);

# a: Element of ConicAlg
# j, l: 1, 2, or 3 such that j <> l
# Returns: a[jl] \in Cubic
# "Mat" stands for the fact that, if we think of the elements of Cubic as matrices,
# this element has a non-zero entry at position j, l.
BindGlobal("CubicConicElMat", function(a, j, l)
	local i;
	if not (l in [1,2,3] and j in [1,2,3] and l <> j) then
		return fail;
	else
		i := Difference([1,2,3], [j,l])[1]; # {1, 2, 3} = {i, j, l} as sets
		if [i, j, l] in CycPerm then
			return CubicConicEl(a, i);
		else
			return CubicConicEl(ConicAlgInv(a), i);
		fi;
	fi;
end);

BindGlobal("CubicConicElOne", function(i)
	return CubicConicEl(One(ConicAlg), i);
end);

BindGlobal("CubicConicElOneMat", function(i, j)
	return CubicConicElMat(One(ConicAlg), i, j);
end);

# i, j: Indices 1, 2 or 3
# a: Element of ComRing or ConicAlg
# Returns: a[ij] \in Cubic
BindGlobal("CubicEl", function(a, i, j)
	if i = j then
		ReqComRingEl(a);
		return CubicComEl(a, i);
	elif i <> j then
		ReqConicAlgEl(a);
		return CubicConicElMat(a, i, j);
	else
		Error("Invalid input");
		return fail;
	fi;
end);

# i, j: Indices 1, 2 or 3
# Returns: 1[ij] \in Cubic
BindGlobal("CubicElOne", function(i, j)
	if i = j then
		return CubicComEl(One(ComRing), i);
	else
		return CubicConicElMat(One(ConicAlg), i, j);
	fi;
end);

# t1, t2, t3: Elements of ComRing
# a1, a2, a3: Elements of ConicAlg
# Returns: t1[11] + t2[22] + t3[33] + a1[23] + a2[31] + a3[12]
BindGlobal("CubicElFromTuple", function(t1, t2, t3, a1, a2, a3)
	return Sum([
		CubicComEl(t1, 1), CubicComEl(t2, 2), CubicComEl(t3, 3),
		CubicConicEl(a1, 1), CubicConicEl(a2, 2), CubicConicEl(a3, 3)
	]);
end);

# i: Integer
# Returns: Put p := 3i+1, q := 3i+2, r := 3i+3. Then the output is
# t_p[11] + t_q[22] + t_r[33] + a_p[23] + a_q[31] + a_r[12]
# where t_l and a_l are the respective indeterminates.
BindGlobal("CubicGenericEl", function(i)
	if 3*i+3 > ConicAlg_rank or 3*i+3 > ComRing_rank then
		return fail;
	else
		return CubicElFromTuple(
			ComRingIndet(3*i+1), ComRingIndet(3*i+2), ComRingIndet(3*i+3),
			ConicAlgIndet(3*i+1), ConicAlgIndet(3*i+2), ConicAlgIndet(3*i+3)
		);
	fi;
end);

# i: Integer.
# Returns: A list of the six generic basic elements of Cubic,
# using indeterminates a_i and t_i.
BindGlobal("CubicGensAsModule", function(i)
	local a, t;
	t := ComRingIndet(i);
	a := ConicAlgIndet(i);
	return [
		CubicComEl(t, 1), CubicComEl(t, 2), CubicComEl(t, 2),
		CubicConicEl(a, 1), CubicConicEl(a, 2), CubicConicEl(a, 3)
	];
end);

# ----- Summands -----

# DeclareOperation("SummandsWithPos", [IsCubicElement]);
DeclareOperation("Summands", [IsCubicElement]);

# cubicEl: Element of Cubic.
# Returns: List with (at most 6) entries of the form [i, j, a]. Here a is an
# element in ComRing or ConicAlg. The sum of all elements a[ij] equals cubicEl.
InstallMethod(Summands, [IsCubicElement], function(cubicEl)
	local result, i, a, t;
	result := [];
	for i in [1..3] do
		t := CubicComPart(cubicEl, i);
		if not IsZero(t) then
			Add(result, [i, i, t]);
		fi;
	od;
	for i in [1..3] do
		a := CubicConicPart(cubicEl, i);
		if not IsZero(a) then
			Add(result, [CycPerm[i][2], CycPerm[i][3], a]);
		fi;
	od;
	return result;
end);


# ----- Structural maps of the cubic norm structure ------

DeclareOperation("CubicNorm", [IsCubicElement]);
DeclareOperation("CubicAdj", [IsCubicElement]);
DeclareOperation("CubicCross", [IsCubicElement, IsCubicElement]);
DeclareOperation("CubicBiTr", [IsCubicElement, IsCubicElement]);

# A: Element of Cubic.
# Returns: N(A) \in ComRing, the norm of A.
# [GPR24, (36.4.5)]
InstallMethod(CubicNorm, [IsCubicElement], function(A)
	local sum, perm, i, j, l, prod;
	sum := Sum([
		CubicComPart(A, 1) * CubicComPart(A, 2) * CubicComPart(A, 3),
		Product([
			TwistDiag[1] * TwistDiag[2] * TwistDiag[3],
			ConicAlgTr(CubicConicPart(A, 1)*CubicConicPart(A, 2)*CubicConicPart(A, 3))
		])
	]);
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		prod := Product([
			CubicComPart(A, i) * TwistDiag[j] * TwistDiag[l],
			ConicAlgNorm(CubicConicPart(A, i))
		]);
		sum := sum - prod;
	od;
	return sum;
end );

# A: Element of Cubic.
# Returns: A^#, the adjoint of A.
# [GPR24, (36.4.4)]
InstallMethod(CubicAdj, [IsCubicElement], function(A)
	local result, perm, i, j, l, a_i, a_j, a_l, A_i, A_j, A_l, comEl, algEl;
	result := CubicZero;
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		a_i := CubicConicPart(A, i);
		a_j := CubicConicPart(A, j);
		a_l := CubicConicPart(A, l);
		A_i := CubicComPart(A, i);
		A_j := CubicComPart(A, j);
		A_l := CubicComPart(A, l);
		comEl := A_j*A_l - TwistDiag[j]*TwistDiag[l]*ConicAlgNorm(a_i);
		result := result + CubicComEl(comEl, i);
		algEl := -A_i*a_i + TwistDiag[i] * ConicAlgInv(a_j*a_l);
		result := result + CubicConicElMat(algEl, j, l);
	od;
	return result;
end );

# A, B: Elements of Cubic.
# Returns: A \times B \in Cubic'
# [GPR24, 36.4.6]
InstallMethod(CubicCross, [IsCubicElement, IsCubicElement], function(A, B)
	local result, perm, i, j, l, a_i, a_j, a_l, b_i, b_j, b_l,
		A_i, A_j, A_l, B_i, B_j, B_l, comEl, algEl;
	result := CubicZero;
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		a_i := CubicConicPart(A, i);
		a_j := CubicConicPart(A, j);
		a_l := CubicConicPart(A, l);
		b_i := CubicConicPart(B, i);
		b_j := CubicConicPart(B, j);
		b_l := CubicConicPart(B, l);
		A_i := CubicComPart(A, i);
		A_j := CubicComPart(A, j);
		A_l := CubicComPart(A, l);
		B_i := CubicComPart(B, i);
		B_j := CubicComPart(B, j);
		B_l := CubicComPart(B, l);
		comEl := A_j*B_l + B_j*A_l - TwistDiag[j]*TwistDiag[l]*ConicAlgNormLin(a_i, b_i);
		result := result + CubicComEl(comEl, i);
		algEl := -A_i*b_i - B_i*a_i + TwistDiag[i]*ConicAlgInv(a_j*b_l + b_j*a_l);
		result := result + CubicConicElMat(algEl, j, l);
	od;
	return result;
end );

# A, B: Elements of Cubic.
# Returns: T(A, B) \in Cubic, the bilinear trace.
# [GRP24, (36.4.7)]
InstallMethod(CubicBiTr, [IsCubicElement, IsCubicElement], function(A, B)
	local result, i, j, l, perm;
	result := Zero(ComRing);
	for perm in CycPerm do
		i := perm[1];
		j := perm[2];
		l := perm[3];
		result := Sum([
			result,
			CubicComPart(A, i)*CubicComPart(B, i),
			TwistDiag[j]*TwistDiag[l]*ConicAlgNormLin(CubicConicPart(A, i), CubicConicPart(B, i))
		]);
	od;
	return result;
end );

# ------- Structural maps of the Jordan algebra Cubic ----

DeclareOperation("JordanU", [IsCubicElement, IsCubicElement]);
DeclareOperation("JordanULin", [IsCubicElement, IsCubicElement, IsCubicElement]);
DeclareOperation("JordanD", [IsCubicElement, IsCubicElement, IsCubicElement]);

# a, b: Elements of Cubic. (More precisely, a \in Cubic, b \in Cubic').
# Returns: U_a(b)
InstallMethod(JordanU, [IsCubicElement, IsCubicElement], function(a, b)
	return CubicBiTr(a,b)*a -CubicCross(CubicAdj(a), b);
end );

# a, b,c: Elements of Cubic. (More precisely, a, b \in Cubic, c \in Cubic').
# Returns: U_{a,b}(c), the linearisation of U_d(e) in d.
InstallMethod(JordanULin, [IsCubicElement, IsCubicElement, IsCubicElement], function(a,b,c)
	return CubicBiTr(a, c)*b + CubicBiTr(b, c)*a - CubicCross(CubicCross(a,b), c);
end );

# a, b,c: Elements of Cubic. (More precisely, a, c \in Cubic, b \in Cubic').
# Returns: D_{a,b}(c) = {a, b, c} = U_{a,c}(b)
InstallMethod(JordanD, [IsCubicElement, IsCubicElement, IsCubicElement], function(a,b,c)
	return JordanULin(a,c,b);
end );
