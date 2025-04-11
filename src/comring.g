BaseRing := Rationals;
# ComRing contains indeterminates t_1, ..., t_{ComRing_rank}, g_1, ..., g_3 and
# the norms and traces of elements of ConicAlg
ComRing_rank := 6;
# Let t = Trace_MaxLength. For all k <= t and all i_1, ..., i_k in [ 1..ConicAlg_rank ],
# an indeterminate which represents tr(a_{i_1} ... a_{i_t}) will be created.
# If longer products are needed during the runtime, then an error message is printed.
Trace_MaxLength := 5;
# Dictionary with precomputed values for all traces. Will be initalised later.
_TrDict := fail;

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

ComRingBasicIndet := function(i)
	return Indeterminate(BaseRing, ComRingBasicIndetName(i));
end;

ComRingNormIndet := function(i)
	return Indeterminate(BaseRing, ComRingNormIndetName(i));
end;

ComRingGamIndet := function(i)
	return Indeterminate(BaseRing, ComRingGamIndetName(i));
end;

# --- Norm on ConicAlgMag ---

# mRep: ExtRepOfObj of an element of ConicAlgMag
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

ConicAlgMagNorm := function(m)
	return ConicAlgMagNormOnRep(ExtRepOfObj(m));
end;

### --- Trace on ConicAlgMag ---

## Helper functions

# a, b, c: External reps of elements of ConicAlgMag.
# Output: If one of the elements (repr. by) a,b,c is the conjugate of another, the output
# is a list [ x, y] where x is (the rep of) such an element and y is (the rep of)
# the remaining (third) element.
# Otherwise the output is fail.
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
# Output: The trace of the corresponding element.
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

_ConicAlgMagTrUncached := function(magEl)
	return ConicAlgMagTrOnRep(ExtRepOfObj(magEl));
end;

ConicAlgMagTr := function(magEl)
	return LookupDictionary(_TrDict, magEl);
end;

# Initialises the dictionary with precomputed trace values.
# Returns the maximal indeterminate number that appears in ComRing
_InitTrDict := function()
	local maxIndetNum, magEl, magEls, trace, polyRep, monomial, i, j;
	# Initialise all the other indeterminates of ComRing so that they occupy the
	# first indeterminate indices
	for i in [1..ComRing_rank] do
		ComRingBasicIndet(i);
	od;
	for i in [1..ConicAlg_rank] do
		ComRingNormIndet(i);
	od;
	for i in [1..3] do
		ComRingGamIndet(i);
	od;
	# Initialise dictionary
	maxIndetNum := 0;
	magEls := Concatenation(_AllConicAlgMagEls(Trace_MaxLength));
	magEls := Concatenation([One(ConicAlgMag)], magEls);
	_TrDict := NewDictionary(magEls[1], true, magEls);
	for magEl in magEls do
		trace := _ConicAlgMagTrUncached(magEl);
		AddDictionary(_TrDict, magEl, trace);
		polyRep := ExtRepNumeratorRatFun(trace);
		for i in [1..Length(polyRep)/2] do
			# Iterate through all monomials in trace
			monomial := polyRep[2*i - 1];
			for j in [1..Length(monomial)/2] do
				# Iterate through all indeterminate numbers in monomial
				maxIndetNum := Maximum(maxIndetNum, monomial[2*j - 1]);
			od;
		od;
	od;
	return maxIndetNum;
end;

_ComRingNumIndets := _InitTrDict();
ComRing := FunctionField(BaseRing, _ComRingNumIndets);