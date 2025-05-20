
## Definition of ConicAlg

ConicAlg := FreeMagmaRing(ComRing, ConicAlgMag);
ConicAlgMagToAlg := x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x);
ConicAlgElFam := FamilyObj(Zero(ConicAlg));

ConicAlgMagEmb := x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x);
ConicAlgIndets := List(ConicAlgMagIndets, ConicAlgMagEmb);

ConicAlgBasicIndets := ConicAlgIndets{[1..ConicAlg_rank]};
ConicAlgInvIndets := ConicAlgIndets{[ConicAlg_rank+1..2*ConicAlg_rank]};

## Functions which test requirements and throw errors

DeclareOperation("ReqComRingEl", [IsRingElement]);
DeclareOperation("ReqComRingEl", [IsList]);
DeclareOperation("ReqConicAlgEl", [IsRingElement]);
DeclareOperation("ReqConicAlgEl", [IsList]);

InstallMethod(ReqComRingEl, [IsRingElement], function(a)
	if skip_tests then
		return true;
	fi;
	if not IsRationalFunction(a) then
		Display(a);
		Error("Invalid input: Must be in ComRing.");
		return false;
	fi;
	return true;
end);
InstallMethod(ReqComRingEl, [IsList], function(list)
	local a;
	for a in list do
		if not ReqComRingEl(a) then
			return false;
		fi;
	od;
	return true;
end);

InstallMethod(ReqConicAlgEl, [IsRingElement], function(a)
	if skip_tests then
		return true;
	fi;
	if not a in ConicAlg then
		Display(a);
		Error("Invalid input: Must be in ConicAlg.");
		return false;
	fi;
	return true;
end);
InstallMethod(ReqConicAlgEl, [IsList], function(list)
	local a;
	for a in list do
		ReqConicAlgEl(a);
	od;
end);

## Constructors for indeterminates

ConicAlgBasicIndet := function(i)
	return ConicAlgBasicIndets[i];
end;

ConicAlgInvIndet := function(i)
	return ConicAlgInvIndets[i];
end;

## Functions on the rings

ConicAlgInv := function(a)
	ReqConicAlgEl(a);
	return ChangeRingElByMagmaTrans(ConicAlg, a, ConicAlgMagInv);
end;

# magFunc: A function ConicAlgMag -> ComRing.
# Output: The linear extension ConicAlg -> Comring of magFunc.
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

ConicAlgTr := ConicAlgFunctionalFromMagFunctional(ConicAlgMagTr);

# a, b: Element of ConicAlg.
# Output: n(a,b) such that n(a+b) = n(a) + n(b) + n(a,b).
# By [GPR24, (16.12.4), (16.5.2)], we have n(a,b) = n(1, a'b) = t(a'b)
ConicAlgNormLin := function(a, b)
	ReqConicAlgEl([a,b]);
	return ConicAlgTr(ConicAlgInv(a)*b);
end;

# a: Element of ConicAlg.
# Output: Its norm, an element of ComRing.
ConicAlgNorm := function(a)
	local coeffList, result, i, j, magmaEl, magmaEl2, coeff, coeff2;
	ReqConicAlgEl(a);
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

# Initialises the lists _ComRingTraceIndets and _ConicAlgTraces
_InitTraceIndets := function()
	local i, infoList, type, info, a, aInv;
	_ComRingTraceIndets := [];
	_ConicAlgTraces := [];
	for i in [1..Length(_ComRingIndetInfo)] do
		infoList := _ComRingIndetInfo[i];
		type := infoList[1];
		info := infoList[2];
		if type = "tr" then
			Add(_ComRingTraceIndets, Indeterminate(BaseRing, i));
			a := ConicAlgMagEmb(info); # \in ConicAlg
			aInv := ConicAlgMagEmb(ConicAlgMagInv(a));
			Add(_ConicAlgTraces, a+ConicAlgInv(a));
		fi;
	od;
end;

_InitTraceIndets();

### Simplifier

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
# Output: The same element but with ComRingCancel applied to all ComRing-coefficients
DeclareOperation("ComRingCancel", [IsElementOfFreeMagmaRing]);
InstallMethod(ComRingCancel, [IsElementOfFreeMagmaRing], function(a)
	local coeffMagList, resultCoeffList, resultMagList, i;
	coeffMagList := CoefficientsAndMagmaElements(a);
	resultCoeffList := [];
	resultMagList := [];
	for i in [1..Length(coeffMagList)/2] do
		Add(resultMagList, coeffMagList[2*i-1]); # Magma element
		Add(resultCoeffList, ComRingCancel(coeffMagList[2*i])); # Coefficient
	od;
	return ElementOfMagmaRing(FamilyObj(a), Zero(ComRing), resultCoeffList, resultMagList);
end);