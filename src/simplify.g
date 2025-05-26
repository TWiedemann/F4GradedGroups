### Functions that return elements which are mathematically equivalent to the input
### but have a simpler representation.
### The function Simplify is available for each structure and applies all available
### simplification functions except for WithoutTraces because WithoutTraces is
### not always a desirable transformation.

## -------- ComRing --------

# a: Element of a.
# Output: The same element, but all coefficients are multiplied by the lcm of all
# denominators (so that only integers appear) and then divided by the gcd of the
# remaining coefficients.
DeclareOperation("ComRingCancel", [IsRationalFunction]);
InstallMethod(ComRingCancel, [IsRationalFunction], function(a)
	# local fam, numRep, denRep, num, den, gcd, gcdRep, newNumRep, newDenRep;
	local fam, numRep, denRep, denLcm, gcd, i, newNumRep, newDenRep;
	fam := FamilyObj(a);
	numRep := ExtRepNumeratorRatFun(a);
	denRep := ExtRepDenominatorRatFun(a);
	# If denominator is trivial, no extra work is necessary
	if denRep = [[], 1] then
		return a;
	fi;
	# Compute the lcm of the denominators appearing in numRep and denrep
	denLcm := 1;
	for i in [1..Length(denRep)/2] do
		denLcm := Lcm(denLcm, DenominatorRat(denRep[2*i]));
	od;
	for i in [1..Length(numRep)/2] do
		denLcm := Lcm(denLcm, DenominatorRat(numRep[2*i]));
	od;
	# Compute the gcd of all coeff*denLcm where coeff runs through all coefficients
	# appearing in numRep and denRep
	gcd := denRep[2]*denLcm;
	for i in [2..Length(denRep)/2] do
		gcd := Lcm(gcd, NumeratorRat(numRep[2*i]*denLcm));
	od;
	for i in [1..Length(denRep)/2] do
		gcd := Lcm(gcd, NumeratorRat(denRep[2*i]*denLcm));
	od;
	# Create new representations in which each coefficient is multiplied by
	# denLcm/gcd
	newNumRep := [];
	for i in [1..Length(numRep)/2] do
		Add(newNumRep, numRep[2*i-1]);
		Add(newNumRep, numRep[2*i]*denLcm/gcd);
	od;
	newDenRep := [];
	for i in [1..Length(denRep)/2] do
		Add(newDenRep, denRep[2*i-1]);
		Add(newDenRep, denRep[2*i]*denLcm/gcd);
	od;
	if newDenRep = [[], 1] then
		# trivial denominator
		return PolynomialByExtRep(fam, newNumRep);
	else
		return RationalFunctionByExtRep(fam, newNumRep, newDenRep);
	fi;
end);

DeclareOperation("ComRingSimplifyTr", [IsRationalFunction]);
InstallMethod(ComRingSimplifyTr, [IsRationalFunction], function(a)
	return Value(a, _TrSubIndetList, _TrSubValueList, One(ComRing));
end);

DeclareOperation("Simplify", [IsRationalFunction]);
InstallMethod(Simplify, [IsRationalFunction], function(a)
	return ComRingCancel(ComRingSimplifyTr(a));
end);

## -------- ConicAlg --------

# a: Element of ComRing.
# Output: The element obtained from a by replacing each occurence of tr(a) by a+a'.
# In particular, the output lies in ConicAlg.
DeclareOperation("WithoutTraces", [IsRationalFunction]);
InstallMethod(WithoutTraces, [IsRationalFunction], function(a)
	local coeffList, result, i, magEl, comEl;
	ReqComRingEl(a);
	return Value(a, _ComRingTraceIndets, _ConicAlgTraces, One(ConicAlg));
end);

# a: Element of ConicAlg.
# Output: The element obtained from a by applying WithoutTraces to all ComRing-coefficients.
# The output lies in ConicAlg.
DeclareOperation("WithoutTraces", [IsElementOfFreeMagmaRing]);
InstallMethod(WithoutTraces, [IsElementOfFreeMagmaRing], function(a)
	local coeffList, result, i, magEl, comEl;
	ReqConicAlgEl(a);
	coeffList := CoefficientsAndMagmaElements(a);
	result := Zero(ConicAlg);
	for i in [1..Length(coeffList)/2] do
		magEl := coeffList[2*i - 1];
		comEl := coeffList[2*i];
		result := result + WithoutTraces(comEl) * ConicAlgMagEmb(magEl);
	od;
	return result;
end);

# a: Element of ConicAlg.
# Output: The same element but with Simplify applied to all ComRing-coefficients
DeclareOperation("Simplify", [IsElementOfFreeMagmaRing]);
InstallMethod(Simplify, [IsElementOfFreeMagmaRing], function(a)
	local coeffMagList, resultCoeffList, resultMagList, i;
	coeffMagList := CoefficientsAndMagmaElements(a);
	resultCoeffList := [];
	resultMagList := [];
	for i in [1..Length(coeffMagList)/2] do
		Add(resultMagList, coeffMagList[2*i-1]); # Magma element
		Add(resultCoeffList, Simplify(coeffMagList[2*i])); # Coefficient
	od;
	return ElementOfMagmaRing(FamilyObj(a), Zero(ComRing), resultCoeffList, resultMagList);
end);

## -------- Cubic --------

# Apply WithoutTraces to all ConicAlg-components
DeclareOperation("WithoutTraces", [IsCubicElement]);
InstallMethod(WithoutTraces, [IsCubicElement], function(cubEl)
	return CubicElFromTuple(
		CubicElComCoeff(cubEl, 1), CubicElComCoeff(cubEl, 2), CubicElComCoeff(cubEl, 3),
		WithoutTraces(CubicElAlgCoeff(cubEl, 1)),
		WithoutTraces(CubicElAlgCoeff(cubEl, 2)),
		WithoutTraces(CubicElAlgCoeff(cubEl, 3))
	);
end);

# Applies Simplify to all components.
DeclareOperation("Simplify", [IsCubicElement]);
InstallMethod(Simplify, [IsCubicElement], function(cubEl)
	local t, a, i;
	t := [];
	a := [];
	for i in [1..3] do
		t[i] := Simplify(CubicElComCoeff(cubEl, i));
		a[i] := Simplify(CubicElAlgCoeff(cubEl, i));
	od;
	return CubicElFromTuple(t[1], t[2], t[3], a[1], a[2], a[3]);
end);

## -------- Brown --------

# Apply WithoutTraces to all ConicAlg-components
DeclareOperation("WithoutTraces", [IsBrownElement]);
InstallMethod(WithoutTraces, [IsBrownElement], function(brownEl)
	return BrownElFromTuple(
		BrownElPart(brownEl, 1),
		WithoutTraces(BrownElPart(brownEl, 2)),
		WithoutTraces(BrownElPart(brownEl, 3)),
		BrownElPart(brownEl, 4)
	);
end);

# Applies Simplify to all components.
DeclareOperation("Simplify", [IsBrownElement]);
InstallMethod(Simplify, [IsBrownElement], function(brownEl)
	local t, cub, i;
	t := [];
	cub := [];
	for i in [1, 2] do
		t[i] := Simplify(BrownElComPart(brownEl, i));
		cub[i] := Simplify(BrownElCubicPart(brownEl, i));
	od;
	return BrownElFromTuple(t[1], cub[1], cub[2], t[2]);
end);

## -------- DD --------

# Helper functions for ApplyDistAndPeirceLaw

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
# Output: A list [i, j, c, coeffs, lConic, rConic] where {i, j} = {i1, j1}, i < j,
# coeffs, lConic, rConic are lists of the same length, c \in ConicAlg,
# the elements of coeffs are in ComRing and the elements of lConic, rConic are monimals in ConicAlg,
# and dd(x1, x2) = dd_{1[ij],c[ji]}+\sum_{k=1}^{Length(coeffs)} coeffs[k]*dd((lConic[k])[ij], (rConic[k])[ji]).
# Further, for all k we have (lConic[k] <> 1 implies rConic[k] <> 1) and
# (lConic[k] = 1 implies coeffs[k] = 1). This says that whenever we have only one
# non-zero coefficient from ConicAlg, we apply relations to ensure that the
# non-zero coefficients appears on the right-hand side and that the coefficient
# from ComRing is pulled into the coefficient from ConicAlg (via c*dd_{1,a} = dd_{1,c*a}).
_ApplyDistAndPeirceLaw_OnSummands_int2 := function(i1, j1, a, i2, j2, b)
	local i, j, coeffs, lConic, rConic, aCoeffList, aCoeff, bCoeff, bCoeffList,
		aMag, bMag, aTwist, p, q, c;
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
	## Return values
	coeffs := [];
	lConic := [];
	rConic := [];
	# All summands coeff*dd_{1[ij],a[ji]} are combined as dd_{1[ij], c[ji]}
	c := Zero(ConicAlg);
	## Split up a and b into sums of monomials
	aCoeffList := CoefficientsAndMagmaElements(a);
	bCoeffList := CoefficientsAndMagmaElements(b);
	for p in [1..Length(aCoeffList)/2] do
		for q in [1..Length(bCoeffList)/2] do
			aCoeff := aCoeffList[2*p]; # in ComRing
			bCoeff := bCoeffList[2*q]; # in ComRing
			aMag := aCoeffList[2*p - 1]; # in ConicAlgMag
			bMag := bCoeffList[2*q - 1]; # in ConicAlgMag
			if aMag = One(ConicAlgMag) then
				c := c + aCoeff*bCoeff*ConicAlgMagToAlg(bMag);
			elif bMag = One(ConicAlgMag) then
				# Use relation dd_{a[ij],1[ji]} = dd_{1[ij],a[ji]}
				c := c + aCoeff*bCoeff*ConicAlgMagToAlg(aMag);
			else
				Add(coeffs, aCoeff*bCoeff);
				Add(lConic, ConicAlgMagToAlg(aMag));
				Add(rConic, ConicAlgMagToAlg(bMag));
			fi;
		od;
	od;
	return [i, j, c, coeffs, lConic, rConic];
end;

# ddEl: Element of DD.
# Output: An element of DD+ComRing*xi+ComRing*zeta (internally, an element of L0)
# which (mathematically) represents the same element, but simplified:
# 1. For each i <> j, there is at most one summands from Z_{i \to j}, and it is
# of the form d_{1[ii], c[ij]} for some c in ConicAlg.
# 2. For each i, there is at most one summand from Z_{ii,ii}, and it is
# of the form d_{1[ii], t[ii]} for some t in ComRing.
# 3. For each i<j, there is at most one summand of the form d_{1[ij],a[ji]}.
# Every other summand in Z_{ij,ji} is of the form t*d_{a[ij],b[ji]} where
# t \in ComRing and a, b \in ConicAlg are monomial (i.e., lie in the image of ConicAlgMag)
# with a <> 1 and b <> 1.
# 4. Summands from Z_{ij,kl} with Intersection([i,j], [k,l]) = [] are removed.
# If applyDDRels = true, then by applying certain relations in L0, we achieve that
# the output has the following additional properties:
# - it has no summand of the form d_{1[33],t[33]}.
# - it has not summand of the form d_{a[ij],a'[ji]}.
# - in all summands of the form d_{1[ij],a[ji]} with a \in ConicAlg,
# a has no summand of the form t*1 for t \in ComRing.
# See [DMW, 3.8, 5.2, 5.20] for the mathematical justification.
DeclareOperation("ApplyDistAndPeirceLaw", [IsDDElement, IsBool]);
InstallMethod(ApplyDistAndPeirceLaw, [IsDDElement, IsBool], function(ddEl, applyDDRels)
	local resultZto, resultRemainCoeffList, resultCoeffList, ddSummand, ddCoeff,
		cubic1, cubic2, cubSummandList1, cubSummandList2, i1, j1, a, i2, j2, b,
		intersection, simp, i, j, coeffs, lCubic, rCubic, k, resultZShift, c, t,
		xiCoeff, zetaCoeff, list, lConic, rConic, add;
	# resultZto[i][j] will store an element x of ConicAlg or of ComRing such that the result has a
	# summand dd(1[ii], x[ij]) \in Z_{i \to j}
	resultZto := [
		[Zero(ComRing), Zero(ConicAlg), Zero(ConicAlg)],
		[Zero(ConicAlg), Zero(ComRing), Zero(ConicAlg)],
		[Zero(ConicAlg), Zero(ConicAlg), Zero(ComRing)]
	];
	# resultZShift[i][j] for i<j will store an element x of ConicAlg such that
	# the result has a summand dd(1[ij],x[ji]).
	resultZShift := [
		[, Zero(ConicAlg), Zero(ConicAlg)],
		[,, Zero(ConicAlg)]
	];
	# All remaining summands (as DDCoeffList). I.e., those that lie in Z_{ij,ji} for some i <> j
	# and which cannot be expressed as dd(1[ij],b[ji])
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
                # Consider the summand ddCoeff*dd(a[i1,j1], b[i2,j2])
				if Size(intersection) = 1 then
					simp := _ApplyDistAndPeirceLaw_OnSummands_int1(i1, j1, a, i2, j2, ddCoeff*b);
					i := simp[1];
					j := simp[2];
                    c := simp[3];
                    # The summand equals dd(1[ii], c[ij])
					resultZto[i][j] := resultZto[i][j] + c;
				elif Size(intersection) = 2 then
					simp := _ApplyDistAndPeirceLaw_OnSummands_int2(i1, j1, a, i2, j2, ddCoeff*b);
					i := simp[1];
					j := simp[2];
					c := simp[3];
					coeffs := simp[4];
					lConic := simp[5];
					rConic := simp[6];
					if i<j then
						resultZShift[i][j] := resultZShift[i][j] + c;
					else
						resultZShift[i][j] := resultZShift[i][j] + ConicAlgInv(c);
					fi;
					for k in [1..Length(coeffs)] do
						if applyDDRels and lConic[k] = ConicAlgInv(rConic[k]) then
							# Apply relation
							# d(a[ij],a'[ji]) = g_i g_j n(a) (d(1[ii],1[ii]) + d(1[jj],1[jj]))
							add := coeffs[k]*ComRingGamIndet(i)
									*ComRingGamIndet(j)*ConicAlgNorm(lConic[k]);
							resultZto[i][i] := resultZto[i][i] + add;
							resultZto[j][j] := resultZto[j][j] + add;
						else
							lCubic := CubicAlgElMat(i, j, lConic[k]);
							rCubic := CubicAlgElMat(j, i, rConic[k]);
							Add(resultRemainCoeffList, [coeffs[k], lCubic, rCubic]);
						fi;
					od;
				fi;
				# If intersection is empty, the summand is zero and we do nothing
			od;
		od;
	od;

    # Apply DD-relations
	xiCoeff := Zero(ComRing);
	zetaCoeff := Zero(ComRing);
    if applyDDRels then
		# Replace dd(1[ij],c*1[ji]) for c \in ComRing by
		# c*g_i*g_j*(dd(1[ii],1[ii])+dd(1[jj],1[jj]))
		for i in [1,2] do
			for j in [i+1..3] do
				list := ConicAlgSplitOne(resultZShift[i][j]);
				t := list[1];
				c := list[2];
				# resultZShift[i][j] = t*1 + c
				resultZto[i][i] := resultZto[i][i] + t*ComRingGamIndet(i)*ComRingGamIndet(j);
				resultZto[j][j] := resultZto[j][j] + t*ComRingGamIndet(i)*ComRingGamIndet(j);
				resultZShift[i][j] := c;
			od;
		od;
        # Replace dd(1[33], c[33]) by c*((2\zeta-\xi) - dd(1[11], 1[11]) - dd(1[22], 1[22]))
        zetaCoeff := 2*resultZto[3][3];
        xiCoeff := -resultZto[3][3];
        resultZto[1][1] := resultZto[1][1] - resultZto[3][3];
        resultZto[2][2] := resultZto[2][2] - resultZto[3][3];
        resultZto[3][3] := Zero(ComRing);
    fi;

	# Finalise coefficient list of the result
	resultCoeffList := [];
	for i in [1..3] do
		for j in [1..3] do
			Add(resultCoeffList, [
				One(ComRing), CubicComElOne(i),
				CubicElMat(i, j, resultZto[i][j])
			]);
			if i<j then
				Add(resultCoeffList, [
					One(ComRing), CubicAlgElOneMat(i,j), 
					CubicElMat(j, i, resultZShift[i][j])
				]);
			fi;
		od;
	od;
	resultCoeffList := Concatenation(resultCoeffList, resultRemainCoeffList);

	if _SanitizeImmediately then
		DDSanitizeRep(resultCoeffList);
	fi;
	
	return DDToL0Emb(DD(resultCoeffList)) + xiCoeff*L0Xi + zetaCoeff*L0Zeta;
end);

# Apply WithoutTraces to all ConicAlg-components
DeclareOperation("WithoutTraces", [IsDDElement]);
InstallMethod(WithoutTraces, [IsDDElement], function(dd)
	local coeffList, newCoeffList, list;
	coeffList := DDCoeffList(dd);
	newCoeffList := [];
	for list in coeffList do
		Add(newCoeffList, [list[1], WithoutTraces(list[2]), WithoutTraces(list[3])]);
	od;
	return DDElFromCoeffList(newCoeffList);
end);

# Applies Simplify to all components.
# Does NOT apply ApplyDistAndPeirceLaw because the output would be in L0, not in DD.
DeclareOperation("Simplify", [IsDDElement]);
InstallMethod(Simplify, [IsDDElement], function(ddEl)
	local coeffList, resultCoeffList, list;
	# ddEl := ApplyDistAndPeirceLaw(ddEl, false);
	coeffList := DDCoeffList(ddEl);
	resultCoeffList := [];
	for list in coeffList do
		Add(resultCoeffList,
			[Simplify(list[1]), Simplify(list[2]), Simplify(list[3])]
		);
	od;
	return DDElFromCoeffList(resultCoeffList);
end);

## -------- L0 --------

# L0el: Element of L0.
# Output: The same element with ApplyDistAndPeirceLaw applied to the DD-part.
# Usually not needed because Simplify also applies ApplyDistAndPeirceLaw to the DD-part.
DeclareOperation("ApplyDistAndPeirceLaw", [IsL0Element, IsBool]);
InstallMethod(ApplyDistAndPeirceLaw, [IsL0Element, IsBool], function(L0el, applyDDRels)
	local rep;
	rep := StructuralCopy(UnderlyingElement(L0el));
	rep.dd := ApplyDistAndPeirceLaw(rep.dd, applyDDRels);
	return L0(rep);
end);

# Apply WithoutTraces to all ConicAlg-Components
DeclareOperation("WithoutTraces", [IsL0Element]);
InstallMethod(WithoutTraces, [IsL0Element], function(l0El)
	return Sum([
		CubicPosToL0Emb(WithoutTraces(L0CubicPosCoeff(l0El))),
		CubicNegToL0Emb(WithoutTraces(L0CubicNegCoeff(l0El))),
		L0XiCoeff(l0El)*L0Xi,
		L0ZetaCoeff(l0El)*L0Zeta,
		DDToL0Emb(WithoutTraces(L0DDCoeff(l0El)))
	]);
end);

# Applies Simplify to all components and applies ApplyDistAndPeirceLaw to the DD-part.
DeclareOperation("Simplify", [IsL0Element]);
InstallMethod(Simplify, [IsL0Element], function(L0El)
	local pos, neg, zeta, xi, dd, l0;
	pos := L0CubicPosCoeff(L0El);
	neg := L0CubicNegCoeff(L0El);
	zeta := L0ZetaCoeff(L0El);
	xi := L0XiCoeff(L0El);
	l0 := ApplyDistAndPeirceLaw(L0DDCoeff(L0El), true);
	return Sum([
		CubicPosToL0Emb(Simplify(pos)),
		CubicNegToL0Emb(Simplify(neg)),
		Simplify(zeta + L0ZetaCoeff(l0)) * L0Zeta,
		Simplify(xi + L0XiCoeff(l0)) * L0Xi,
		DDToL0Emb(Simplify(L0DDCoeff(l0)))
	]);
end);

## -------- Lie --------

# lieEl: Element of Lie.
# Output: The same element with ApplyDistAndPeirceLaw applied to the DD-part.
# Usually not needed because Simplify also applies ApplyDistAndPeirceLaw to the DD-part.
DeclareOperation("ApplyDistAndPeirceLaw", [IsLieElement, IsBool]);
InstallMethod(ApplyDistAndPeirceLaw, [IsLieElement, IsBool], function(lieEl, applyDDRels)
	local rep;
	rep := StructuralCopy(UnderlyingElement(lieEl));
	rep.zero := ApplyDistAndPeirceLaw(rep.zero, applyDDRels);
	return Lie(rep);
end);

# Apply WithoutTraces to all ConicAlg-components
DeclareOperation("WithoutTraces", [IsLieElement]);
InstallMethod(WithoutTraces, [IsLieElement], function(lieEl)
	return LieElFromTuple(
		LiePart(lieEl, -2),
		WithoutTraces(LiePart(lieEl, -1)),
		WithoutTraces(LiePart(lieEl, 0)),
		WithoutTraces(LiePart(lieEl, 1)),
		LiePart(lieEl, 2)
	);
end);

# Applies Simplify to all components.
DeclareOperation("Simplify", [IsLieElement]);
InstallMethod(Simplify, [IsLieElement], function(lieEl)
	local parts, i;
	parts := [];
	for i in [-2..2] do
		Add(parts, Simplify(LiePart(lieEl, i)));
	od;
	return LieElFromTuple(parts[1], parts[2], parts[3], parts[4], parts[5]);
end);

## -------- LieEndo --------

DeclareOperation("Simplify", [IsLieEndo]);
InstallMethod(Simplify, [IsLieEndo], function(lieEndo)
	return LieEndo(
		function(lieEl)
			return Simplify(lieEndo(lieEl));
		end
	);
end);
