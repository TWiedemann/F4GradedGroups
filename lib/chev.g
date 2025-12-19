### This file contains the definition of the Chevalley-type basis of Lie and function
### which compute its structure constants.
### It also contains a "Chevalley basis of type G2".

## -------- Chevalley basis of Lie --------

# root: Root in F4
# Returns: The corresponding element of a "Chevalley basis" of Lie
ChevBasEl := function(root)
	local one;
	if root in F4ShortRoots then
		one := One(ConicAlg);
	elif root in F4LongRoots then
		one := One(ComRing);
	else
		return fail;
	fi;
	return LieRootHomF4(root, one);
end;

# root: Root in G2.
# Returns: The corresponding element of a "Chevalley basis" of type G2 of Lie.
ChevG2BasEl := function(root)
	local F4root, result, sign;
	if root in G2LongRoots then
		# Additional minus sign
		if root in [[-2,-1], [-1,-2]] then
			sign := -1;
		else
			sign := 1;
		fi;
		# Find corresponding F4-root
		for F4root in F4LongRoots do
			if F4RootG2Coord(F4root) = root then
				return sign*LieRootHomF4(F4root, One(ComRing), true, true);
			fi;
		od;
	else
		# Add F4-basis elements for all long roots in the preimage of root
		result := LieZero;
		for F4root in F4LongRoots do
			if F4RootG2Coord(F4root) = root then
				result := result + LieRootHomF4(F4root, One(ComRing), true, true);
			fi;
		od;
		if root in [[-1,0], [0,-1]] then
			sign := -1;
		else
			sign := 1;
		fi;
		return sign*result;
	fi;
end;

# root: Root in F4.
# Returns: The element h_root of the Chevalley basis.
ChevHEl := function(root)
	return ChevBasEl(root) * ChevBasEl(-root);
end;

# root: Root in G2.
# Returns: The element h_root of the Chevalley basis.
ChevG2HEl := function(root)
	return ChevG2BasEl(root) * ChevG2BasEl(-root);
end;

# root1, root2: Roots in F4
# Returns: Integer c s.t. [ x_root1, x_root2 ] = c x_{root1+root2}.
# Here x_a = ChevBasEl(a) and the output is 0 if root1+root2 is not a root.
ChevStrucConst := function(root1, root2)
	local sum, candidates, comm, chevSum, c, diff;
	sum := root1+root2;
	if not sum in F4Roots then
		return Zero(ComRing);
	fi;
	# Since ComRing is not a field, it is not evident that there even exists c \in ComRing
	# such that [ x_root1, x_root2 ] = c x_{root1+root2}. Hence we cannot use GAP functions
	# to immediately obtain c. However, it turns out that there is only a low number of
	# possibilities which may occur, so we simply try them all out.
	candidates := [-2,-1,1,2];
	comm := ChevBasEl(root1) * ChevBasEl(root2);
	chevSum := ChevBasEl(sum);
	for c in candidates do
		if Simplify(comm - c*chevSum) = LieZero then
			return c;
		fi;
	od;
	return fail;
end;

# root1, root2: Roots in G2
# Returns: Integer c s.t. [ x_root1, x_root2 ] = c x_{root1+root2}.
# Here x_a = ChevBasEl(a) and the output is 0 if root1+root2 is not a root.
ChevG2StrucConst := function(root1, root2)
	local sum, candidates, comm, chevSum, c, diff;
	sum := root1+root2;
	if not sum in G2Roots then
		return Zero(ComRing);
	fi;
	candidates := [-4,-3,-2,-1,1,2,3,4];
	comm := ChevG2BasEl(root1) * ChevG2BasEl(root2);
	chevSum := ChevG2BasEl(sum);
	for c in candidates do
		if Simplify(comm - c*chevSum) = LieZero then
			return c;
		fi;
	od;
	return fail;
end;
