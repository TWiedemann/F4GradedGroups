
## ComRing indeterminates

# i: Integer.
# Output: Name of the i-th indeterminate of ComRing.
ComRingBasicIndetName := function(i)
	return Concatenation("t", String(i));
end;

# i: Integer with 1 <= i <= ConicAlg_rank.
# Output: The name of the indeterminate of ComRing which represents the norm of a_i
ComRingNormIndetName := function(i)
	if i in [1..ConicAlg_rank] then
		return Concatenation("n(", ConicAlgIndetNames[i], ")");
	else
		return fail;
	fi;
end;

# The elements \gamma_1, ..., \gamma_3 of the diagonal matrix \Gamma which "twists"
# the cubic Jordan matrix algebra.
ComRingGamIndetName := function(i)
	if i in [1, 2, 3] then
		return Concatenation("g", String(i));
	else
		return fail;
	fi;
end;

# ai \in ComRing
ComRingBasicIndet := function(i)
	return Indeterminate(BaseRing, ComRingBasicIndetName(i));
end;

# n(ai) \in ComRing
ComRingNormIndet := function(i)
	return Indeterminate(BaseRing, ComRingNormIndetName(i));
end;

# gi \in ComRing
ComRingGamIndet := function(i)
	return Indeterminate(BaseRing, ComRingGamIndetName(i));
end;

# --- Norm on ConicAlgMag ---

# mRep: ExtRepOfObj of an element of ConicAlgMag
# Output: Norm of this element (as an element of ComRing)
ConicAlgMagNormOnRep := function(mRep)
	if mRep = 0 then # n(1_ConicAlg) = 1_ComRing
		return One(PolynomialRing(BaseRing));
	elif mRep in [1..ConicAlg_rank] then
		return ComRingNormIndet(mRep);
	elif mRep in [ConicAlg_rank+1..2*ConicAlg_rank] then
		return ComRingNormIndet(mRep - ConicAlg_rank);
	elif IsList(mRep) then
		return ConicAlgMagNormOnRep(mRep[1]) * ConicAlgMagNormOnRep(mRep[2]);
	else
		return fail;
	fi;
end;

# m: Element of ConicAlgMag
# Output: norm of m (\in ComRing)
ConicAlgMagNorm := function(m)
	return ConicAlgMagNormOnRep(ExtRepOfObj(m));
end;

### --- Trace on ConicAlgMag ---

## Helper functions

# a, b, c: External reps of elements of ConicAlgMag.
# Output: If one of the elements (repr. by) a,b,c is the conjugate of another, the output
# is a list [ x, y] where x is the rep of such an element and y is the rep of
# the remaining (third) element.
# Otherwise the output is fail.
# Example: _PullNorm([1, 2], [3], [5, 4]) is [[1, 2], [3]] or [[5,4], [3]] if 1' = 4 and 2' = 5
_PullNorm := function(a, b, c)
    local list, i, j, k;
	list := [a,b,c];
	for i in [1..3] do
		for j in [i+1..3] do
			if list[i] = ConicAlgMagInvOnRep(list[j]) then
				k := Difference([1..3], [i,j])[1];
				return [list[i], list[k]];
			fi;
		od;
	od;
	return fail;
end;

# a, b, c: External reps of elements of ConicAlgMag
# Output: List of triples [d, e, f] s.t. tr(abc) = tr(def)
_ConicAlgMagTrCandidates := function(a, b, c)
	local aInv, bInv, cInv;
	aInv := ConicAlgMagInvOnRep(a);
	bInv := ConicAlgMagInvOnRep(b);
	cInv := ConicAlgMagInvOnRep(c);
	return [
		[a, b, c], [b, c, a], [c, a, b],
		[cInv, bInv, aInv], [aInv, cInv, bInv], [bInv, aInv, cInv]
	];
end;

# mRep: External rep of an element of ConicAlgMag
# Output: The trace of the corresponding element. No caching of results.
ConicAlgMagTrOnRep := function(mRep)
	local indetName, varName, inv, left, right, candidates, list, min, StringFromRep;
	indetName := "tr(";
	inv := ConicAlgMagInvOnRep;
	if not IsList(mRep) then
		if mRep = 0 then
			return 2*One(PolynomialRing(BaseRing)); # tr(1) = 2
		else
			mRep := Minimum(mRep, ConicAlgMagInvOnRep(mRep)); # Replace a' by a if necessary
			indetName := Concatenation(indetName, String(ConicAlgMagElFromRep(mRep)));
		fi;
	else
		left := mRep[1];
		right := mRep[2];
		if left = ConicAlgMagInvOnRep(right) then
			return 2*ConicAlgMagNormOnRep(left);
		fi;
		# A "candidate" is a triple [a,b,c] of reps such that tr(mRep) = tr(abc).
		# We first compute all candidates and then choose the minimal one (w.r.t lex).
		if not (IsList(left) or IsList(right)) then
			candidates := [
				[left, right], [right, left], [inv(left), inv(right)], [inv(right), inv(left)]
			];
		else
			candidates := [];
			if IsList(left) then
				list := _PullNorm(left[1], left[2], right);
				if list <> fail then
					return ConicAlgMagNormOnRep(list[1]) * ConicAlgMagTrOnRep(list[2]);
				else
					candidates := Concatenation(
						candidates, _ConicAlgMagTrCandidates(left[1], left[2], right)
					);
				fi;
			fi;
			if IsList(right) then
				list := _PullNorm(left, right[1], right[2]);
				if list <> fail then
					return ConicAlgMagNormOnRep(list[1]) * ConicAlgMagTrOnRep(list[2]);
				else
					candidates := Concatenation(
						candidates, _ConicAlgMagTrCandidates(left, right[1], right[2])
					);
				fi;
			fi;
		fi;
		min := Minimum(candidates);
		# Note: String puts a bracket around elements of ConicAlgMag if their
		# length is at least 2
		varName := Concatenation(List(min, x -> String(ConicAlgMagElFromRep(x))));
        indetName := Concatenation(indetName, varName);
	fi;
	indetName := Concatenation(indetName, ")");
	return Indeterminate(BaseRing, indetName);
end;

# magEl: Element of ConicAlgMag
# Output: Its trace (an element of ComRing). No caching.
_ConicAlgMagTrUncached := function(magEl)
	return ConicAlgMagTrOnRep(ExtRepOfObj(magEl));
end;

# Same as _ConicAlgMagTrUncached, but returns the precomputed, cached result.
ConicAlgMagTr := function(magEl)
	return LookupDictionary(_TrDict, magEl);
end;

_ComRingGamIndetNum := []; # Contains the indeterminate number of gamma_i at position i

# Initialises:
# - the dictionary _TrDict with precomputed trace values.
# - the list _ComRingIndetInfo
# For a documentation, see read.g.
# Returns the maximal indeterminate number that appears in ComRing
_InitDicts := function()
	local maxIndetNum, magEl, magEls, trace, polyRep, monomial, i, j;
	_ComRingIndetInfo := [];
	# Initialise all the other indeterminates of ComRing in the desired order
	for i in [1..3] do
		ComRingGamIndet(i);
		_ComRingGamIndetNum[i] := i;
		Add(_ComRingIndetInfo, ["g", i]);
	od;
	for i in [1..ComRing_rank] do
		ComRingBasicIndet(i);
		Add(_ComRingIndetInfo, ["t", i]);
	od;
	for i in [1..ConicAlg_rank] do
		ComRingNormIndet(i);
		Add(_ComRingIndetInfo, ["n", ConicAlgMagBasicIndet(i)]);
	od;
	# Initialise dictionary
	maxIndetNum := 3 + ComRing_rank + ConicAlg_rank;
	magEls := Concatenation(_AllConicAlgMagEls(Trace_MaxLength));
	magEls := Concatenation([One(ConicAlgMag)], magEls);
	_TrDict := NewDictionary(magEls[1], true, magEls);
	for magEl in magEls do
		trace := _ConicAlgMagTrUncached(magEl);
		AddDictionary(_TrDict, magEl, trace);
		## Update maxIndetNum
		polyRep := ExtRepNumeratorRatFun(trace);
		# Iterate through all monomials in trace
		for i in [1..Length(polyRep)/2] do
			monomial := polyRep[2*i - 1];
			# Iterate through all indeterminate numbers in monomial
			for j in [1..Length(monomial)/2] do
				if monomial[2*j-1] > maxIndetNum then
					# A new indeterminate has occured.
					maxIndetNum :=  monomial[2*j - 1];
					Add(_ComRingIndetInfo, ["tr", magEl]);
				fi;
			od;
		od;
	od;
	return maxIndetNum;
end;

_ComRingNumIndets := _InitDicts();
ComRing := FunctionField(BaseRing, _ComRingNumIndets);

# a: Element of a.
# Output: The same element, but the gcd(numerator, denominator) has been cancelled
DeclareOperation("ComRingCancel", [IsRationalFunction]);
InstallMethod(ComRingCancel, [IsRationalFunction], function(a)
	local fam, numRep, denRep, num, den, gcd, gcdRep, newNumRep, newDenRep;
	fam := FamilyObj(a);
	numRep := ExtRepNumeratorRatFun(a);
	denRep := ExtRepDenominatorRatFun(a);
	num := PolynomialByExtRep(fam, numRep);
	den := PolynomialByExtRep(fam, denRep);
	gcd := Gcd(num, den);
	gcdRep := ExtRepNumeratorRatFun(gcd);
	newNumRep := QuotientPolynomialsExtRep(fam, numRep, gcdRep);
	newDenRep := QuotientPolynomialsExtRep(fam, denRep, gcdRep);
	if newDenRep = [[], 1] then
		# trivial denominator
		return PolynomialByExtRep(fam, newNumRep);
	else
		return RationalFunctionByExtRep(fam, newNumRep, newDenRep);
	fi;
end);

# Function that cancels gamma_i if possible. GAP does not automatically
# recognise that e.g. (g1*g2)/(g1*g3) can be simplified to g2/g3.
# ComRingCancelGam := function(t)
#
# 	fam := FamilyObj(t);
# 	numRep := ExtRepNumeratorRatFun(t)
# 	denRep := ExtRepNumeratorRatFun(t);
# 	# We only cancel if the denominator is a monomial
# 	if Length(denRep) <> 2 then
# 		return t;
# 	fi;
# 	denMonoRep := denRep[1];
# end;