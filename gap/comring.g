### This file contains the definition of ComRing, the polynomial ring over Z
### that represents an arbitrary commutative ring, and functions related to it

# ----- Indeterminates names -----

# Indeterminate names for traces are defined further below because this is more complicated.

# i: Integer.
# Returns: Name of the i-th indeterminate of ComRing which represents an arbitrary element.
BindGlobal("_ComRingIndetName", function(i)
	return Concatenation("t", String(i));
end);

# i: Integer with 1 <= i <= ConicAlg_rank.
# Returns: The name of the indeterminate of ComRing which represents the norm of a_i
BindGlobal("_ComRingNormIndetName", function(i)
	if i in [1..ConicAlg_rank] then
		return Concatenation("n(", _ConicAlgIndetName(i), ")");
	else
		return fail;
	fi;
end);

# i: 1, 2, or 3
# Returns: The name of the indeterminate which represents \gamma_i, the i-th
# element of the diagonal matrix \Gamma which "twists" the cubic Jordan matrix algebra.
BindGlobal("ComRingGamIndetName", function(i)
	if i in [1, 2, 3] then
		return Concatenation("g", String(i));
	else
		return fail;
	fi;
end);

# ----- Indeterminates

# t_i \in ComRing, represents arbitrary element of ComRing
BindGlobal("ComRingIndet", function(i)
	return Indeterminate(ComRingBaseRing, _ComRingIndetName(i));
end);

# n(a_i) \in ComRing, represents norm of conic algebra element a_i
BindGlobal("ComRingNormIndet", function(i)
	return Indeterminate(ComRingBaseRing, _ComRingNormIndetName(i));
end);

# g_i \in ComRing, represents \gamma_i
BindGlobal("ComRingGamIndet", function(i)
	return Indeterminate(ComRingBaseRing, ComRingGamIndetName(i));
end);

# ----- Norm: ConicAlgMag -> ComRing -----

# mRep: ExtRepOfObj of an element of ConicAlgMag
# Returns: Norm of this element (as an element of ComRing)
DeclareGlobalName("ConicAlgMagNormOnRep");
BindGlobal("ConicAlgMagNormOnRep", function(mRep)
	if mRep = 0 then # n(1_ConicAlg) = 1_ComRing
		return One(PolynomialRing(ComRingBaseRing));
	elif mRep in [1..ConicAlg_rank] then
		return ComRingNormIndet(mRep);
	elif mRep in [ConicAlg_rank+1..2*ConicAlg_rank] then
		return ComRingNormIndet(mRep - ConicAlg_rank);
	elif IsList(mRep) then
		return ConicAlgMagNormOnRep(mRep[1]) * ConicAlgMagNormOnRep(mRep[2]);
	else
		return fail;
	fi;
end);

# m: Element of ConicAlgMag
# Returns: norm of m, an element of ComRing
BindGlobal("ConicAlgMagNorm", function(m)
	return ConicAlgMagNormOnRep(ExtRepOfObj(m));
end);

# ----- Trace: ConicAlgMag -> ComRing -----

# The trace map is slightly complicated because there exist relations such as
# tr(ab)=tr(ba) and tr((ab)c) = tr(a(bc)). We try to use these relations to keep
# the number of necessary indeterminates low.

## Helper functions for trace

# a, b, c: External reps of elements of ConicAlgMag.
# Returns: If one of the elements (repr. by) a,b,c is the conjugate of another, the output
# is a list [x, y] where x is the rep of such an element and y is the rep of
# the remaining (third) element.
# Otherwise the output is fail.
# Example: If ConicAlg_rank = 3 (so that a1'=a4 and a2'=a5), then
# _PullNorm([1, 2], [3], [5, 4]) is [[1, 2], [3]] or [[5,4], [3]]
# The point of this is that the elements tr(aa'b), tr(a'ba), tr(baa') all equal
# n(a)tr(b), i.e., we can "pull norms out of traces".
# This is a helper function to detect this and bring the input in a usable format.
BindGlobal("_PullNorm", function(a, b, c)
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
end);

# a, b, c: External reps of elements of ConicAlgMag
# Returns: List of triples [d, e, f] s.t. tr(abc) = tr(def).
# By the relations tr(ab) = tr(ba), tr((ab)c) = tr(a(bc)) and tr(a') = tr(a),
# we may write tr(abc) without brackets and this term is equal to all cyclic permutations
# and to all cyclic permutations of tr(c'b'a').
BindGlobal("_ConicAlgMagTrCandidates", function(a, b, c)
	local aInv, bInv, cInv;
	aInv := ConicAlgMagInvOnRep(a);
	bInv := ConicAlgMagInvOnRep(b);
	cInv := ConicAlgMagInvOnRep(c);
	return [
		[a, b, c], [b, c, a], [c, a, b],
		[cInv, bInv, aInv], [aInv, cInv, bInv], [bInv, aInv, cInv]
	];
end);

# mRep: External rep of an element of ConicAlgMag
# Returns: An element of ComRing which represents the trace of the corresponding
# element of ConicAlgMag. In most cases, this is an indeterminate in ComRing,
# but it need not be. E.g. tr(One(ConicAlgMag)) = 2*One(ComRing).
# We use the relations described in _ConicAlgMagTrCandidates and _PullNorm.
DeclareGlobalName("_ConicAlgMagTrUncachedOnRep");
BindGlobal("_ConicAlgMagTrUncachedOnRep", function(mRep)
	local indetName, varName, inv, left, right, candidates, list, min, StringFromRep;
	indetName := "tr(";
	inv := ConicAlgMagInvOnRep;
	if not IsList(mRep) then
		if mRep = 0 then
			return 2*One(PolynomialRing(ComRingBaseRing)); # tr(1) = 2
		else
			mRep := Minimum(mRep, ConicAlgMagInvOnRep(mRep)); # Replace a' by a if necessary
			indetName := Concatenation(indetName, String(ConicAlgMagElFromRep(mRep)));
		fi;
	else
		left := mRep[1];
		right := mRep[2];
		if left = ConicAlgMagInvOnRep(right) then
			return 2*ConicAlgMagNormOnRep(left); # tr(aa') = 2n(a)
		fi;
		# A "candidate" is a triple [a,b,c] of reps such that tr(mRep) = tr(abc).
		# Note that tr((ab)c) = tr(a(bc)), so no brackets are necessary.
		# Compute all candidates
		if not IsList(left) and not IsList(right) then
			# tr(ab) = tr(ba) and tr(a') = tr(a)
			candidates := [
				[left, right], [right, left], [inv(left), inv(right)], [inv(right), inv(left)]
			];
		else
			candidates := [];
			if IsList(left) then
				list := _PullNorm(left[1], left[2], right);
				if list <> fail then
					# Pull out norms: E.g. tr(aa'b) = n(a)tr(b). Apply recursion to compute tr(b).
					return ConicAlgMagNormOnRep(list[1]) * _ConicAlgMagTrUncachedOnRep(list[2]);
				else
					# No pulling out of norms is possible
					candidates := Concatenation(
						candidates, _ConicAlgMagTrCandidates(left[1], left[2], right)
					);
				fi;
			fi;
			if IsList(right) then
				# As above, but with left and right switched
				list := _PullNorm(left, right[1], right[2]);
				if list <> fail then
					return ConicAlgMagNormOnRep(list[1]) * _ConicAlgMagTrUncachedOnRep(list[2]);
				else
					candidates := Concatenation(
						candidates, _ConicAlgMagTrCandidates(left, right[1], right[2])
					);
				fi;
			fi;
		fi;
		# Choose the minimal candidate w.r.t the lex order. It does not matter which
		# one we choose, but this is an easy way to choose a unique representative.
		min := Minimum(candidates); # minimum w.r.t. lex order
		# If min = [a, b, c], then varName = "abc". Note that 
		# String puts a bracket around elements of ConicAlgMag if their length
		# is at least 2, so we do not have to do this ourselves.
		# E.g. if min = [a1, a1a2, a3], then varName = "a1(a1a2)a3"
		varName := Concatenation(List(min, x -> String(ConicAlgMagElFromRep(x))));
        indetName := Concatenation(indetName, varName);
	fi;
	indetName := Concatenation(indetName, ")");
	return Indeterminate(ComRingBaseRing, indetName);
end);

# magEl: Element of ConicAlgMag
# Returns: Its trace (an element of ComRing). No caching.
BindGlobal("_ConicAlgMagTrUncached", function(magEl)
	return _ConicAlgMagTrUncachedOnRep(ExtRepOfObj(magEl));
end);

# rep: Representation of an element of ConicAlgMag
# Returns: Its precomputed trace (an element of ComRing), which we cache.
BindGlobal("ConicAlgMagTrOnRep", function(rep)
	if _CacheTrace then
		return LookupDictionary(_TrDict, rep);
	else
		return _ConicAlgMagTrUncachedOnRep(rep);
	fi;
end);

# Same as _ConicAlgMagTrUncached, but returns the precomputed, cached result.
BindGlobal("ConicAlgMagTr", function(magEl)
	return ConicAlgMagTrOnRep(ExtRepOfObj(magEl));
end);

# a, b: Elements of ConicAlgMag.
# Returns: n(a,b) := n(a+b) - n(a) - n(b).
# By [GPR24, (16.12.4), (16.5.2)], we have n(a,b) = n(1, a'b) = t(a'b)
BindGlobal("ConicAlgMagNormLin", function(a, b)
	return ConicAlgMagTr(ConicAlgMagInv(a)*b);
end);

# _ComRingGamIndetNum := []; # Contains the indeterminate number of gamma_i at position i (not used)

# Initialises:
# - the dictionary _TrDict with precomputed trace values.
# - the list _ComRingIndetInfo
# - Every indeterminate that may appear in ComRing is created once, and this always happens
# in the same order (for a fixed choice of ConigAlg_rank and Trace_MaxLength). Every indeterminate
# is assigned a number by GAP the first time it is used. Calling this function ensures that
# the indeterminates are always initialised in the same order and hence always have the same
# internal number. This guarantees that they are always printed in the same order. Hence it
# is necessary to call this function even if _CacheTrace = false.
# For a documentation of _TrDict and _ComRingIndetInfo, see read.g.
BindGlobal("_InitTrDict", function()
	local maxIndetNum, magEl, magEls, magElsReps, magElRep, trace, polyRep, monomial, i, j;
	BindGlobal("_ComRingIndetInfo", []);
	# Initialise all the other indeterminates of ComRing in the desired order
	for i in [1..3] do
		ComRingGamIndet(i); # Initialise indeterminate
		# _ComRingGamIndetNum[i] := i;
		Add(_ComRingIndetInfo, ["g", i]);
	od;
	for i in [1..ComRing_rank] do
		ComRingIndet(i); # Initialise indeterminate
		Add(_ComRingIndetInfo, ["t", i]);
	od;
	for i in [1..ConicAlg_rank] do
		ComRingNormIndet(i); # Initialise indeterminate
		Add(_ComRingIndetInfo, ["n", ConicAlgMagIndet(i)]);
	od;
	## Initialise dictionary
	# maxIndetNum will be increased whenever a new indeterminate is created
	maxIndetNum := 3 + ComRing_rank + ConicAlg_rank;
	# List of all elements of ConicAlgMag up to length Trace_MaxLength
	magEls := Concatenation(_AllConicAlgMagEls(Trace_MaxLength));
	magEls := Concatenation([One(ConicAlgMag)], magEls);
	magElsReps := List(magEls, x -> ExtRepOfObj(x));
	# New lookup dictionary for keys such as magElsReps[1]. All keys
	# have to lie in magElsReps.
	BindGlobal("_TrDict", NewDictionary(magElsReps[1], true, magElsReps));
	for i in [1..Length(magEls)] do
		magEl := magEls[i];
		magElRep := magElsReps[i];
		trace := _ConicAlgMagTrUncached(magEl);
		AddDictionary(_TrDict, magElRep, trace);
		## Update maxIndetNum
		polyRep := ExtRepNumeratorRatFun(trace); # rep of the polynomial trace
		# Iterate through all monomials in trace
		for i in [1..Length(polyRep)/2] do
			monomial := polyRep[2*i - 1];
			# Iterate through all indeterminate numbers in monomial
			for j in [1..Length(monomial)/2] do
				if monomial[2*j-1] > maxIndetNum then
					# A new indeterminate has occured. It must be tr(magEl).
					maxIndetNum :=  monomial[2*j - 1];
					Add(_ComRingIndetInfo, ["tr", magEl]);
				fi;
			od;
		od;
	od;
	return maxIndetNum;
end);

BindGlobal("_ComRingNumIndets", _InitTrDict());
BindGlobal("ComRing", FunctionField(ComRingBaseRing, _ComRingNumIndets));
