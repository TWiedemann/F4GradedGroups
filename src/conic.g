## Definition of ConicAlg

ConicAlg := FreeMagmaRing(ComRing, ConicAlgMag);
ConicAlgMagToAlg := x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x);
ConicAlgElFam := FamilyObj(Zero(ConicAlg));


embConicAlgMag := x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x);
ConicAlgIndets := List(ConicAlgMagIndets, embConicAlgMag);


ConicAlgBasicIndets := ConicAlgIndets{[1..ConicAlg_rank]};
ConicAlgInvIndets := ConicAlgIndets{[ConicAlg_rank+1..2*ConicAlg_rank]};

## Functions which test requirements and throw errors

DeclareOperation("ReqComRingEl", [IsRingElement]);
DeclareOperation("ReqComRingEl", [IsList]);
DeclareOperation("ReqConicAlgEl", [IsRingElement]);
DeclareOperation("ReqConicAlgEl", [IsList]);

InstallMethod(ReqComRingEl, [IsRingElement], function(a)
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
	return changeRingElByMagmaTrans(ConicAlg, a, ConicAlgMagInv);
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