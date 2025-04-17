SanitizeImmediately := true; # If true, DDSanitizeRep is applied after several transformations which may produce unsanitized (but correct) output

# DD is the ComRing-span of all dd_{a,b} for a, b \in Cubic.
# An element t1 * dd_{a1, b1} + t2 * dd_{a2, b2} + ... is represented by
# the list [[t1, a1, b2], [t2, a2, b2], ...].

DDSanitizeRep := function(rep)
	local i, j, x;
	for i in [Length(rep), Length(rep)-1 .. 1] do
		if i > Length(rep) then
			# This may happen because we remove elements from rep during the loop
			continue;
		fi;
		x := rep[i];
		if x[1] = Zero(ComRing) or IsZero(x[2]) or IsZero(x[3]) then
			Remove(rep, i);
			continue;
		fi;
		for j in [1..i-1] do
			if rep[j][2] = x[2] and rep[j][3] = x[3] then
				rep[j][1] := rep[j][1] + x[1];
				Remove(rep, i);
				if rep[j][1] = Zero(ComRing) then
					Remove(rep, j);
				fi;
				break;
			fi;
		od;
	od;
end;

L0ZeroString := "0_{L_0}";
DDSymString := "\dd";

DDRepToString := function(a)
	local stringList, summand, s;
	stringList := [];
	for summand in a do
		s := Concatenation(DDSymString, "_{", String(summand[2]), ",", String(summand[3]), "}");
		if summand[1] <> One(ComRing) then
			s := Concatenation("(", String(summand[1]), ")", "*", s); 
		fi;
		Add(stringList, s);
	od;
	return StringSum(stringList, "+", L0ZeroString);
end;

DDSpec := rec(
	ElementName := "DDElement",
	Zero := a -> [],
	Addition := function(a, b)
		local sum;
		sum := Concatenation(a,b);
		if SanitizeImmediately then
			DDSanitizeRep(sum);
		fi;
		return sum;
	end,
	AdditiveInverse := function(a)
		local inv, i;
		inv := [];
		for i in [1..Length(a)] do
			Add(inv, [-a[i][1], a[i][2], a[i][3]]);
		od;
		return inv;
	end,
	Print := function(a)
		Print(DDRepToString(a));
	end,
	# Lie bracket on DD
	Multiplication := function(a, b)
		local productRep, summand1, summand2, x1, x2, y1, y2, z1, z2, coeff;
		# We do not sanitize the input because, under normal circumstances, it should already
		# be sanitized
		productRep := [];
		for summand1 in a do
			x1 := summand1[2];
			x2 := summand1[3];
			for summand2 in b do
				y1 := summand2[2];
				y2 := summand2[3];
				# summand1*summand2 = coeff * (dd_{D_{x1,x2}(y1), y2} - dd_{y1, D_{x2,x1}(y2)})
				# Here "D" is JordanD
				coeff := summand1[1] * summand2[1]; # in ComRing
				z1 := JordanD(x1, x2, y1);
				z2 := y2;
				if not IsZero(z1) then
					Add(productRep, [coeff, z1, z2]);
				fi;
				z1 := y1;
				z2 := JordanD(x2, x1, y2);
				if not IsZero(z2) then
					Add(productRep, [-coeff, z1, z2]);
				fi;
			od;
		od;
		if SanitizeImmediately then
			DDSanitizeRep(productRep);
		fi;
		return productRep;
	end,
	MathInfo := IsAdditivelyCommutativeElement
);

DD := ArithmeticElementCreator(DDSpec);
InstallMethod(String, [IsDDElement], x -> DDRepToString(UnderlyingElement(x)));

## ---- Getters ----
DeclareOperation("DDCoeffList", [IsDDElement]);

# ddEl: c1*dd_{a1,b1} + c2*dd_{a2,b2} + ...
# Output: [[c1, a1, b1], [c2, a2, b2], ...]
InstallMethod(DDCoeffList, [IsDDElement], function(ddEl)
	return UnderlyingElement(ddEl);
end);

## ---- Constructors ----
DDZero := DD([]);

DeclareOperation("dd", [IsCubicElement, IsCubicElement]);
InstallMethod(dd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	if IsZero(cubicEl1) or IsZero(cubicEl2) then
		return DDZero;
	else
		return DD([[One(ComRing), cubicEl1, cubicEl2]]);
	fi;
end);


# Scalar multiplication ComRing x DD -> DD
InstallOtherMethod(\*, "for ComRingElement and DDElement", [IsRingElement, IsDDElement], 2, function(comEl, ddEl)
	local resultRep, summand;
    ReqComRingEl(comEl);
    resultRep := [];
    for summand in UnderlyingElement(ddEl) do
        Add(resultRep, [comEl*summand[1], summand[2], summand[3]]);
    od; 
	return DD(resultRep);
end);

## ---- Simplifier ----

# i1, j1, i2, j2: Integers in {1,2,3} such that the intersection of {i1, j1}
# and {i2, j2} has exactly one element
# a: Element of ComRing if i1 = j1. Element of ConicAlg otherwise.
# b: Element of ComRing if i2 = j2. Element of ConicAlg otherwise.
# Put x1 := a[i1,j1] = CubicElMat(i1, j1, a) and x2 := b[i2,j2].
# Output: A list [i, j, y] such that
# dd(x1, x2) = dd(CubicElOneMat(i,i), CubicElMat(i, j, y)).
# Here i, j \in {1,2,3} and y \in ComRing if i=j and y \in ConicAlg if i<>j.
_ApplyDistAndPeirceLaw_OnSummands_int1 := function(i1, j1, a, i2, j2, b)
	local p, q, l;
	# Define p, q, l such that dd(x1, y2) lies in Z_{pq,ql}
	q := Intersection([i1, j1], [i2, j2])[1];
	if j1 = q then
		p := i1;
	else
		p := j1;
	fi;
	if i2 = q then
		l := j2;
	else
		l := i2;
	fi;
	# Replace a by ConicAlgInv(a) if necessary to ensure that
	# cubic1 = CubicAlgElMat(p, q, a)
	if i1 <> p then
		# Since { i1, j1 } = { p, q }, we have a in ConicAlg in this case
		a := ConicAlgInv(a);
	fi;
	# Similarly, ensure that cubic2 = CubicAlgElMat(q, l, b)
	if j2 <> l then
		b := ConicAlgInv(b);
	fi;
	
	if q in [p,l] then
		return [p, l, a*b];
	else
		# In this case, we also have p <> l because otherwise,
		# q and p would be two distinct elements in intersection.
		return [p, l, TwistDiag[q]*a*b];
	fi;
end;

# i1, j1, i2, j2: Integers in {1,2,3} such that {i1, j1} = {i2, j2} and i1 <> j1
# a, b: Elements of ConicAlg.
# Put x1 := a[i1,j1] = CubicAlgElMat(i1, j1, a) and x2 := b[i2, j2].
# Output: A list [i, j, coeffs, lConic, rConic] where {i, j} = {i1, j1}, i < j,
# coeffs, lConic, rConic are lists of the same length,
# the elements of coeffs are in ComRing and the elements of lConic, rConic are monimals in ConicAlg,
# and dd(x1, x2) = \sum_{k=1}^{Length(coeffs)} coeffs[k] * dd((lConic[k])[ij], (rConic[k])[ji])
_ApplyDistAndPeirceLaw_OnSummands_int2 := function(i1, j1, a, i2, j2, b)
	local i, j, coeffs, lConic, rConic, aCoeffList, aCoeff, bCoeff, bCoeffList,
		aMonomial, bMonomial, p, q;
	# Define i < j s.t. {i,j} = {i1,j1} and ensure that x1 = a[ij], x2 = b[ji].
	if i1 = j1 or Set([i1, j1]) <> Set([i2, j2]) then
		Error("Invalid input");
		return fail;
	fi;
	if i1 < j1 then
		i := i1;
		j := j1;
	else
		i := j1;
		j := i1;
		a := ConicAlgInv(a);
	fi;
	if i2 <> j then
		b := ConicAlgInv(b);
	fi;
	# Return values
	coeffs := [];
	lConic := [];
	rConic := [];
	# Split up a and b into sums of monomials
	aCoeffList := CoefficientsAndMagmaElements(a);
	bCoeffList := CoefficientsAndMagmaElements(b);
	for p in [1..Length(aCoeffList)/2] do
		for q in [1..Length(bCoeffList)/2] do
			aCoeff := aCoeffList[2*p]; # in ComRing
			bCoeff := bCoeffList[2*q]; # in ComRing
			aMonomial := aCoeffList[2*p - 1]; # in ConicAlgMag
			bMonomial := bCoeffList[2*q - 1]; # in ConicAlgMag
			Add(coeffs, aCoeff*bCoeff);
			Add(lConic, ConicAlgMagToAlg(aMonomial));
			Add(rConic, ConicAlgMagToAlg(bMonomial));
		od;
	od;
	return [i, j, coeffs, lConic, rConic];
end;

# ddEl: Element of DD.
# Output: An element of DD which (mathematically) represents the same element of DD,
# but simplified:
# 1. For each i <> j, there is at most one summands from Z_{i \to j}, and it is
# of the form d_{1[ii], c[ij]} for some c in ConicAlg.
# 2. For each i, there is at most one summand from Z_{ii,ii}, and it is
# of the form d_{1[ii], t[ii]} for some t in ComRing.
# 3. Summands from Z_{ij,ji} for i <> j are of the form t*d_{a[ij],b[ji]} where
# t \in ComRing and a, b \in ConicAlg are monomial (i.e., lie in the image of ConicAlgMag).
# 4. Summands from Z_{ij,kl} with Intersection([i,j], [k,l]) = [] are removed.
# See [DMW, 3.8, 5.2, 5.20] for the mathematical justification.
DeclareOperation("ApplyDistAndPeirceLaw", [IsDDElement]);
InstallMethod(ApplyDistAndPeirceLaw, [IsDDElement], function(ddEl)
	local resultZ, resultRemainCoeffList, resultCoeffList, ddSummand, ddCoeff,
		cubic1, cubic2, cubSummandList1, cubSummandList2, i1, j1, a, i2, j2, b,
		intersection, simp, i, j, coeffs, lCubic, rCubic, k;
	# resultZ[i][j] will store an element x of ConicAlg or of ComRing such that the result has a
	# summand dd(1[ii], x[ij]) \in Z_{i \to j}
	resultZ := [
		[Zero(ComRing), Zero(ConicAlg), Zero(ConicAlg)],
		[Zero(ConicAlg), Zero(ComRing), Zero(ConicAlg)],
		[Zero(ConicAlg), Zero(ConicAlg), Zero(ComRing)]
	];
	# All remaining summands. I.e., those that lie in Z_{ij,ji} for some i <> j
	resultRemainCoeffList := [];
	# Simplify all summands in ddEl
	for ddSummand in DDCoeffList(ddEl) do
		ddCoeff := ddSummand[1];
		cubic1 := ddSummand[2];
		cubic2 := ddSummand[3];
		# Split up the summands of cubic1 and cubic2 (distributive law)
		for cubSummandList1 in Summands(cubic1) do
			for cubSummandList2 in Summands(cubic2) do
				i1 := cubSummandList1[1];
				j1 := cubSummandList1[2];
				a := cubSummandList1[3]; # in ComRing or Conicalg
				i2 := cubSummandList2[1];
				j2 := cubSummandList2[2];
				b := cubSummandList2[3]; # in ComRing or ConicAlg
				intersection := Intersection([i1,j1], [i2,j2]);
				if Size(intersection) = 1 then
					simp := _ApplyDistAndPeirceLaw_OnSummands_int1(i1, j1, a, i2, j2, ddCoeff*b);
					i := simp[1];
					j := simp[2];
					resultZ[i][j] := resultZ[i][j] + simp[3];
				elif Size(intersection) = 2 then
					simp := _ApplyDistAndPeirceLaw_OnSummands_int2(i1, j1, a, i2, j2, ddCoeff*b);
					i := simp[1];
					j := simp[2];
					coeffs := simp[3];
					lCubic := List(simp[4], x -> CubicAlgElMat(i, j, x));
					rCubic := List(simp[5], x -> CubicAlgElMat(j, i, x));
					for k in [1..Length(coeffs)] do
						Add(resultRemainCoeffList, [coeffs[k], lCubic[k], rCubic[k]]);
					od;
				fi;
				# If intersection is empty, the summand is zero and we do nothing
			od;
		od;
	od;

	# Finalise coefficient list of the result
	resultCoeffList := [];
	for i in [1..3] do
		for j in [1..3] do
			Add(resultCoeffList, [One(ComRing), CubicComElOne(i), CubicElMat(i, j, resultZ[i][j])]);
		od;
	od;
	resultCoeffList := Concatenation(resultCoeffList, resultRemainCoeffList);

	if SanitizeImmediately then
		DDSanitizeRep(resultCoeffList);
	fi;
	
	return DD(resultCoeffList);
end);

## ------- Root homomorphisms ----

DeclareOperation("DDRootHomA2", [IsList, IsRingElement]);

# root: A root in A_2.
# a: An element of ConicAlg.
# Output: The a-element in the root space of DD w.r.t root.
InstallMethod(DDRootHomA2, [IsList, IsRingElement], function(root, a)
    local i, j, l;
    ReqConicAlgEl(a);
    # The root space w.r.t. root is Z_{i \to j}
    i := Position(root, 1);
    j := Position(root, -1);
    l := Position(root, 0);
    return dd(CubicComEl(i, One(ComRing)), CubicAlgElMat(i, j, a)); # TODO: Is this correct?
end);