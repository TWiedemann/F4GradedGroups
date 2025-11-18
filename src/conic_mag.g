### This file contains the definition of ConicAlgMag, the free magma consisting
### of products of the ideterminates in the conic algebra, and functions related
### to this magma

# ----- Indeterminates and their names -----

# i: Integer.
# Output: Name of the i-th indeterminate in ConicAlg
ConicAlgIndetName := function(i)
	return Concatenation("a", String(i));
end;

# i: Integer.
# Output: Name of the conjugate of the i-th indeterminate in ConicAlg
ConicAlgInvIndetName := function(i)
	return Concatenation("a", String(i), "'");
end;

# Output: The list of all strings which appear as indeterminate names in ConicAlg
_ConicAlgIndetNames := function()
	local ConicAlgIndetNames, i;
	ConicAlgIndetNames := [];
	for i in [1..ConicAlg_rank] do
		Add(ConicAlgIndetNames, ConicAlgIndetName(i));
	od;
	for i in [1..ConicAlg_rank] do
		Add(ConicAlgIndetNames, ConicAlgInvIndetName(i)); # Conjugation
	od;
	return ConicAlgIndetNames;
end;

ConicAlgIndetNames := _ConicAlgIndetNames();

# ----- ConicAlgMag and its generators ----- 

ConicAlgMag := FreeMagmaWithOne(ConicAlgIndetNames);
ConicAlgMagIndets := GeneratorsOfMagmaWithOne(ConicAlgMag);
ConicAlgMagBasicIndets := ConicAlgMagIndets{[1..ConicAlg_rank]};
ConicAlgMagInvIndets := ConicAlgMagIndets{[ConicAlg_rank+1..2*ConicAlg_rank]};

ConicAlgMagBasicIndet := function(i)
	return ConicAlgMagBasicIndets[i];
end;

ConicAlgMagInvIndet := function(i)
	return ConicAlgMagInvIndets[i];
end;

# ----- Constructing elements from representations and list of all elements -----

# mRep: External representation of an element of ConicAlgMag
# Output: The corresponding element of ConicAlgMag
ConicAlgMagElFromRep := function(mRep)
	return ObjByExtRep(FamilyObj(One(ConicAlgMag)), mRep);
end;

# max_length: Integer at least 1
# Output: A list l of length max_length such that l[k] is a list of all external
# reps of elements of ConicMagEl of length k
_AllConicAlgMagReps := function(max_length)
	local result, i, j, x, y;
	result := [];
	for i in [1..max_length] do
		if i = 1 then
			result[i] := [1..2*ConicAlg_rank];
		else
			result[i] := [];
			for j in [1..i-1] do
				for x in result[j] do
					for y in result[i-j] do
						Add(result[i], [x, y]);
					od;
				od;
			od;
		fi;
	od;
	return result;
end;

# max_length: Integer at least 1
# Output: A list l of length max_length such that l[k] is a list of all
# elements of ConicMagEl of length k
_AllConicAlgMagEls := function(max_length)
	return List(_AllConicAlgMagReps(max_length), x -> List(x, ConicAlgMagElFromRep));
end;

# ----- Involution (i.e. conjugation) of ConicAlgMag -----

# mRep: External rep of an element of ConicAlgMag.
# Output: The external rep of the conjugate of this element.
ConicAlgMagInvOnRep := function(mRep)
	local replaceByList, replaceList;
	mRep := ReverseNonassocList(mRep);
	replaceList := [1..2*ConicAlg_rank];
	replaceByList := Concatenation([ConicAlg_rank+1..2*ConicAlg_rank], [1..ConicAlg_rank]);
	return ReplaceInNonassocList(mRep, replaceList, replaceByList);
end;

# m: Element of ConicAlgMag.
# Output: Conjugate of m.
ConicAlgMagInv := function(m)
	return ConicAlgMagElFromRep(ConicAlgMagInvOnRep(ExtRepOfObj(m)));
end;
