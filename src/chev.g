## -------- Chevalley basis of Lie --------

# root: Root in F4
# Output: The corresponding element of a "Chevalley basis" of Lie
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

# root: Root in F4.
# Output: The element h_root of the Chevalley basis.
ChevHEl := function(root)
	return ChevBasEl(root) * ChevBasEl(-root);
end;

# root1, root2: Roots in F4
# Output: Integer c s.t. [ x_root1, x_root2 ] = c x_{root1+root2}.
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
	candidates := [-4,-3,-2,-1,1,2,3,4];
	comm := ChevBasEl(root1) * ChevBasEl(root2);
	chevSum := ChevBasEl(sum);
	for c in candidates do
		if Simplify(comm - c*chevSum) = LieZero then
			return c;
		fi;
	od;
	return fail;
end;