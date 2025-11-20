### ----- Helper functions of general utility -----

### Functions on strings

# stringList: A (possibly empty) list of non-empty strings.
# plusString: A string for the plus symbol. E.g. could be "+" or " + ".
# zeroString: A string.
# Returns: The string "$stringList[1] + $stringList[2] + ...", or zeroString if stringList is empty
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

# list: Either a single element (e.g. an integer) or a list with exactly 2 entries,
# each of which satisfies the same conditions.
# Returns: The reversed list. E.g. [ [ 1, 2 ], 3 ] -> [ 3, [ 2, 1 ] ]
ReverseNonassocList := function(list)
	if IsList(list) then
		if Length(list) <> 2 then
			return fail;
		else
			return [ ReverseNonassocList(list[2]), ReverseNonassocList(list[1]) ];
		fi;
	else
		return list;
	fi;
end;

# list: External representation of an element of a free magma.
# replaceList, replaceByList: Lists of integers of the same length.
# Returns: The list obtained from list by replacing each entry of the form
# replaceList[k] by replaceByList[k]
ReplaceInNonassocList := function(list, replaceList, replaceByList)
	local l, a, k;
	if not IsList(list) then
		k := Position(replaceList, list);
		if k = fail then
			return list;
		else
			return replaceByList[k];
		fi;
	else
		return List(list, x -> ReplaceInNonassocList(x, replaceList, replaceByList));
	fi;
end;

### Functions on magmas

# MagmaRing: A free magma ring over a magma. The magma is not assumed to be free.
# In particular, it can be a monoid.
# r: An element of another magma ring MagmaRing2.
# magmaFunc: A function from the underlying magma of MagmaRing2 to the magma of MagmaRing.
# Returns: The element obtained from r by applying magmaFunc to each of its "monomials".
# I.e. the output lies in MagmaRing.
# I.e. r = \sum \lambda_a a maps to \sum \lambda_a magmaFunc(a)
ChangeRingElByMagmaTrans := function(MagmaRing, r, magmaFunc)
	local coeffList, i, magmaEl, coeff, newListOfCoeff, newListOfMagmaEl;
	# The decomposition of r into its summands.
	# E.g. if r = x_1 + 2 * x_2 * y_1, then coeffList = [x_1, 1, x_2 * y_1, 2]
	coeffList := CoefficientsAndMagmaElements(r);
	# Go through all summands of r.
	newListOfCoeff := [];
	newListOfMagmaEl := [];
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1];
		coeff := coeffList[2*i];
		Add(newListOfCoeff, coeff);
		Add(newListOfMagmaEl, magmaFunc(magmaEl));
	od;
	return ElementOfMagmaRing(
		FamilyObj(Zero(MagmaRing)), Zero(Integers), newListOfCoeff, newListOfMagmaEl
	);
end;

# ----------
