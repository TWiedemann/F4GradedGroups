BaseRing := Rationals;
# ConicAlg contains indeterminates a_1, ... a_{conicalg_rank} (and their conjugations)
conicalg_rank := 6;
# ComRing contains indeterminates t_1, ..., t_{comring_rank} (and the norms and traces of elements of ConicAlg) 
comring_rank := 6;
# Let t = trace_max_length. For all k <= t and all i_1, ..., i_k in [ 1..conicalg_rank ],
# an indeterminate which represents tr(a_{i_1} ... a_{i_t}) will be created.
# If longer products are needed during the runtime, then an error message is printed.
trace_max_length := 3; 

ConicAlgBasicIndetName := function(i)
	return Concatenation("a", String(i));
end;

ConicAlgBasicInvIndetName := function(i)
	return Concatenation("a", String(i), "'");
end;

conicalgIndetNames := [];
for i in [1..conicalg_rank] do
	Add(conicalgIndetNames, ConicAlgBasicIndetName(i));
od;
for i in [1..conicalg_rank] do
	Add(conicalgIndetNames, ConicAlgBasicInvIndetName(i)); # Conjugation
od;

comRingBasicIndetName := function(i)
	return Concatenation("t", String(i));
end;

comRingNormIndetName := function(i)
	if i in [1..conicalg_rank] then
		return Concatenation("n(", conicalgIndetNames[i], ")");
	elif i in [conicalg_rank+1..2*conicalg_rank] then
		return Concatenation("n(", conicalgIndetNames[i-conicalg_rank], ")");
	else
		return fail;
	fi;
end;

comRingTraceIndetName := function(indexList)
	local name, i;
	if Length(indexList) > trace_max_length then
		Error("Product in trace too long");
		return fail;
	fi;
	name := "tr(";
	for i in indexList do
		if not i in [1..2*conicalg_rank] then
			return fail;
		else
			name := Concatenation(name, conicalgIndetNames[i]);
		fi;
	od;
	name := Concatenation(name, ")");
	return name;
end;

# The elements \gamma_1, ..., \gamma_3 of the diagonal matrix \Gamma which "twists"
# the cubic Jordan matrix algebra.
comRingGamIndetName := function(i)
	if i in [1, 2, 3] then
		return Concatenation("g", String(i));
	else
		return fail;
	fi;
end;

comRingIndetNumberForBasic := function(i)
	return i;
end;

comRingIndetNumberForNorm := function(i)
	return comring_rank + i;
end;

# (Obsolete)
# indexList: A list of integers between -conicalg_rank and 2*conicalg_rank, not containing zero.
# An index i in [1..conicalg_rank] represents a_i, an index conicalg_rank+i in [conicalg_rank+1..2*conicalg_rank]
# represents a_i' and an index i in [-conicalg_rank..-1] represents the index a_{-i}'.
# (I.e. for convenience, we have two formats of representing a_i'.)
comRingIndetNumberForTrace := function(indexList)
	local l, result, i;
	l := Length(indexList);
	# Replace any negative entry i by conicalg_rank-i
	for i in [1..l] do
		if indexList[i] < 0 then
			indexList[i] := conicalg_rank - indexList[i];
		fi;
	od;
	result := comring_rank + conicalg_rank; # Basic indeterminates and norm indeterminates
	for i in [1..l-1] do
		result := result + (2*conicalg_rank)^i; # Trace indeterminates of length i
	od;
	for i in [1..l] do
		result := result + (indexList[i]-1)*(2*conicalg_rank)^(l-i);
	od;
	return result+1;
end;

comRingIndetNames := [];
# Basic indeterminates
for i in [1..comring_rank] do
	Add(comRingIndetNames, Concatenation("t", String(i)));
od;
# Norms
for i in [1..conicalg_rank] do
	Add(comRingIndetNames, comRingNormIndetName(i));
od;
# Traces
for l in [1..trace_max_length] do
	indexList := [];
	for i in [1..l] do
		Add(indexList, 1);
	od;
	Add(comRingIndetNames, comRingTraceIndetName(indexList)); # Add [ 1, ..., 1 ]
	while true do
		# Increase indexList by one step
		for i in [l, l-1 .. 1 ] do
			if indexList[i] < 2*conicalg_rank then
				indexList[i] := indexList[i] + 1;
				for j in [i+1..l] do
					indexList[j] := 1;
				od;
				break;
			elif i = 1 then
				indexList := fail;
			fi;
		od;
		if indexList = fail then
			break;
		else
			Add(comRingIndetNames, comRingTraceIndetName(indexList));
		fi;
	od;
od;
# \Gamma
for i in [1,2,3] do
	Add(comRingIndetNames, comRingGamIndetName(i));
od;

ComRing := PolynomialRing(BaseRing, comRingIndetNames);
ConicAlgMag := FreeMagmaWithOne(conicalgIndetNames);
ConicAlg := FreeMagmaRing(ComRing, ConicAlgMag);

ConicAlgMagIndets := GeneratorsOfMagmaWithOne(ConicAlgMag);
embConicAlgMag := x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x);
ConicAlgIndets := List(ConicAlgMagIndets, embConicAlgMag);

ConicAlgMagBasicIndets := ConicAlgMagIndets{[1..conicalg_rank]};
ConicAlgBasicIndets := ConicAlgIndets{[1..conicalg_rank]};
ConicAlgMagInvIndets := ConicAlgMagIndets{[conicalg_rank+1..2*conicalg_rank]};
ConicAlgInvIndets := ConicAlgIndets{[conicalg_rank+1..2*conicalg_rank]};

a1 := ConicAlg.1;
a2 := ConicAlg.2;
a3 := ConicAlg.3;
t1 := ComRing.1;
t2 := ComRing.2;
t3 := ComRing.3;

ConicAlgBasicIndet := function(i)
	return ConicAlgBasicIndets[i];
end;

ConicAlgInvIndet := function(i)
	return ConicAlgInvIndets[i];
end;

comRingBasicIndet := function(i)
	return Indeterminate(BaseRing, comRingBasicIndetName(i));
end;

comRingNormIndet := function(i)
	return Indeterminate(BaseRing, comRingNormIndetName(i));
end;

comRingTraceIndet := function(indexList)
	return Indeterminate(BaseRing, comRingTraceIndetName(indexList));
end;

comRingGamIndet := function(i)
	return Indeterminate(BaseRing, comRingGamIndetName(i));
end;

ConicAlgMagInv := function(m)
	local replaceList, replaceByList;
	if not m in ConicAlgMag then
		return fail;
	fi;
	m := reverseInMagma(m);
	replaceList := Concatenation(ConicAlgMagBasicIndets, ConicAlgMagInvIndets);
	replaceByList := Concatenation(ConicAlgMagInvIndets, ConicAlgMagBasicIndets);
	return replaceInMagma(ConicAlgMag, m, replaceList, replaceByList);
end;

ConicAlgInv := function(a)
	if not a in ConicAlg then
		return fail;
	fi;
	return changeRingElByMagmaTrans(ConicAlg, a, ConicAlgMagInv);
end;

# magFunc: A function ConicAlgMag -> Comring.
# Outpunt: The linear extension ConicAlg -> Comring of magFunc.
# (This is only used for the trace, which makes it a bit useless. I accidentally thought I could use it for the trace and for the norm, but the norm is of course not linear.)
ConicAlgFunctionalFromMagFunctional := function(magFunc)
	return function(a)
		local coeffList, result, i, magmaEl, coeff;
		coeffList := CoefficientsAndMagmaElements(a);
		result := Zero(ComRing);
		for i in [1..Length(coeffList)/2] do
			magmaEl := coeffList[2*i - 1]; # \in ConicAlgMag
			coeff := coeffList[2*i]; # \in ComRing
			result := result + coeff * magFunc(magmaEl);
		od;
		return result;
	end;
end;



# ConicAlgNorm := ConicAlgFunctionalFromMagFunctional(ConicAlgMagNorm);

ConicAlgMagTrOnRep := function(mRep)
	local assocRep;
	assocRep := assocRepFromNonAssocRep(mRep);
	if IsEmpty(assocRep) then
		return 2*One(ComRing); # Tr(1) = 2
	elif Length(assocRep) = 1 and assocRep[1] in [conicalg_rank+1..2*conicalg_rank] then
		return comRingTraceIndet([ assocRep[1] - conicalg_rank ]); # Tr(a') = Tr(a)
	else
		return comRingTraceIndet(assocRep);
	fi;
end;

ConicAlgMagTr := function(m)
	return ConicAlgMagTrOnRep(ExtRepOfObj(m));
end;

ConicAlgTr := ConicAlgFunctionalFromMagFunctional(ConicAlgMagTr);

ConicAlgBiTr := function(a, b)
	return ConicAlgTr(ConicAlgInv(a)*b);
end;

ConicAlgMagNormOnRep := function(mRep)
	if mRep = 0 then
		return Zero(ComRing);
	elif mRep in [1..2*conicalg_rank] then
		return comRingNormIndet(mRep);
	elif IsList(mRep) then
		return ConicAlgMagNormOnRep(mRep[1]) * ConicAlgMagNormOnRep(mRep[2]);
	else
		return fail;
	fi;
end;

ConicAlgMagNorm := function(m)
	return ConicAlgMagNormOnRep(ExtRepOfObj(m));
end;

ConicAlgNorm := function(a)
	local coeffList, result, i, j, magmaEl, magmaEl2, coeff, coeff2;
	coeffList := CoefficientsAndMagmaElements(a);
	result := Zero(ComRing);
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1]; # \in ConicAlgMag
		coeff := coeffList[2*i]; # \in ComRing
		result := result + coeff^2 * ConicAlgMagNorm(magmaEl); # norm(x_i)
		for j in [i+1..Length(coeffList)/2] do
			magmaEl2 := coeffList[2*j - 1]; # \in ConicAlgMag
			coeff2 := coeffList[2*j]; # \in ComRing
			result := result + coeff*coeff2 * ConicAlgMagTr(magmaEl * ConicAlgMagInv(magmaEl2)); # tr(x_i x_j') = linearisation of norm
		od;
	od;
	return result;
end;