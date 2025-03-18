### ----- Helper functions -----

### Functions on strings

# stringList: A (possibly empty) list of non-empty strings
# plusString: A string for the plus symbol. E.g. could be "+" or " + ".
# Output: The string "$stringList[1] + $stringList[2] + ..."
StringSum := function(stringList, plusString, zeroString)
	local l, s, i;
	l := Length(stringList);
	if l = 0 then
		return zeroString;
	elif l = 1 then
		return stringList[1];
	else
		s := stringList[1];
		for i in [2..l] do
			s := Concatenation(s, plusString, stringList[i]);
		od;
		return s;
	fi;
end;

### Functions on lists

# rep: External representation of an element of a free magma. I.e. either an integer or a list [ rep1, rep2 ] where rep1, rep2 are external representations.
# Output: The corresponding associative list.
# Example: 0 -> [ ], i -> [ i ], [ [ 1, 2 ], 3 ] -> [ 1, 2, 3 ]
assocRepFromNonAssocRep := function(rep)
	if rep = 0 then
		return [];
	elif rep in Integers then
		return [ rep ];
	elif IsList(rep) then
		return Concatenation(assocRepFromNonAssocRep(rep[1]), assocRepFromNonAssocRep(rep[2]));
	else
		return fail;
	fi;
end;

# list: Either a single element (e.g. an integer) or a list with exactly 2 entries, each of which satisfies the same conditions.
# Output: The reversed list. E.g. [ [ 1, 2 ], 3 ] -> [ 3, [ 2, 1 ] ]
reverseNonassocList := function(list)
	if IsList(list) then
		if Length(list) <> 2 then
			return fail;
		else
			return [ reverseNonassocList(list[2]), reverseNonassocList(list[1]) ];
		fi;
	else
		return list;
	fi;
end;

# list: A list.
# i: Integer with 1 <= i <= Length(list)
# Output: [ list[i], list[i+1], ..., list[Length(list)], list[1], ..., list[i-1] ]
swapListAtIndex := function(list, i)
	return Concatenation(list{[i..Length(list)]}, list{[1..i-1]});
end;

### Functions on magmas

# Magma: A free Magma.
# rep: An external representation of an element of Magma.
# replaceList: A sublist of GeneratorsOfMagmaWithOne(Magma). (Consists of magma elements, not of their representations!)
# replaceByList: A list of elements in some magma such that Length(replaceByList) = Length(replaceList). (Consists of magma elements, not of their representations!)
# Output: The represenation of the magma element which is obtained from the original element (described by rep) by replacing each occurence of replaceList[k] by replaceByList[k].
replaceInMagmaOnRep := function(Magma, rep, replaceList, replaceByList)
	local k, genMagma, replaceGenNumList, left, right;
	if Length(replaceList) <> Length(replaceByList) then
		return fail;
	fi;
	genMagma := GeneratorsOfMagmaWithOne(Magma);
	replaceGenNumList := List(replaceList, x -> Position(genMagma, x)); # replaceGenNumList is exactly the list replaceList but with each magma element replaced by its generator number in genMagma.
	if IsList(rep) then
		left := replaceInMagmaOnRep(Magma, rep[1], replaceList, replaceByList);
		right := replaceInMagmaOnRep(Magma, rep[2], replaceList, replaceByList);
		# If e.g. left = 0, then left represents the identity element, so we return right instead of [ 0, right ].
		if left = 0 then
			return right;
		elif right = 0 then
			return left;
		else
			return [left, right];
		fi;
	elif rep = 0 then # if magEl = 1
		return 0; # return representation of One(replaceByList[1]);
	else # if rep is a generator
		k := Position(replaceGenNumList, rep);
		if k <> fail then # if k appears in replaceGenNumList
			return ExtRepOfObj(replaceByList[k]);
		else # otherwise leave rep unchanged
			return rep;
		fi;
	fi;
end;

# Magma: A free Magma.
# magEl: An element of Magma.
# replaceList: A sublist of GeneratorsOfMagmaWithOne(Magma).
# replaceByList: A list of elements in some magma such that Length(replaceByList) = Length(replaceList).
replaceInMagma := function(Magma, magEl, replaceList, replaceByList)
	return ObjByExtRep(FamilyObj(One(Magma)), replaceInMagmaOnRep(Magma, ExtRepOfObj(magEl), replaceList, replaceByList));
end;

# m: An element of a free magma.
# Output: The "reversed" element, e.g. (x_1*x_2)*x_3 -> x_3*(x_2*x_1).
reverseInMagma := function(m)
	return ObjByExtRep(FamilyObj(m), reverseNonassocList(ExtRepOfObj(m)));
end;

# MagmaRing: A free magma ring over a magma. The magma is not assumed to be free. In particular, it can be a monoid.
# r: An element of another magma ring MagmaRing2.
# magmaFunc: A function from the underlying magma of MagmaRing2 to the magma of MagmaRing.
# Output: The element obtained from r by applying magmaFunc to each of its "monomials". I.e. the output lies in MagmaRing.
changeRingElByMagmaTrans := function(MagmaRing, r, magmaFunc)
	local coeffList, i, magmaEl, coeff, newListOfCoeff, newListOfMagmaEl;
	coeffList := CoefficientsAndMagmaElements(r); # The decomposition of r into its summands. E.g. if r = x_1 + 2 * x_2 * y_1, then coeffList = [x_1, 1, x_2 * y_1, 2]
	# Go through all summands of r.
	newListOfCoeff := [];
	newListOfMagmaEl := [];
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1];
		coeff := coeffList[2*i];
		Add(newListOfCoeff, coeff);
		Add(newListOfMagmaEl, magmaFunc(magmaEl));
	od;
	return ElementOfMagmaRing(FamilyObj(Zero(MagmaRing)), Zero(Integers), newListOfCoeff, newListOfMagmaEl);
end;



readAll := function()
	Read("/cygdrive/c/Users/Torben/OneDrive/Dokumente/F4-Konstruktion/Brown algebra/F4-5Grading.g");
	Read("/cygdrive/c/Users/Torben/OneDrive/Dokumente/F4-Konstruktion/Brown algebra/helper.g");
	Read("/cygdrive/c/Users/Torben/OneDrive/Dokumente/F4-Konstruktion/Brown algebra/conic.g");
	Read("/cygdrive/c/Users/Torben/OneDrive/Dokumente/F4-Konstruktion/Brown algebra/cubic.g");
	Read("/cygdrive/c/Users/Torben/OneDrive/Dokumente/F4-Konstruktion/Brown algebra/struc.g");
end;

# ----------