windows := true;

myFilePath := function(s)
	if windows then
		return Concatenation("C:/Users/Torben/Documents/Repositories/F4-graded-groups/src/", s);
	else
		return Concatenation("./", s);
	fi;
end;

myUnbind := function(s)
	if IsBoundGlobal(s) then
		MakeReadWriteGlobal(s);
		UnbindGlobal(s);
	fi;
end;

# Reread("F4-5Grading.g");
Reread(myFilePath("F4-roots.g"));
Reread(myFilePath("helper.g"));
Reread(myFilePath("conic.g"));
myUnbind("IsCubicElement");
Reread(myFilePath("cubic.g"));
myUnbind("IsBrownElement");
Reread(myFilePath("brown.g"));
myUnbind("IsDDElement");
myUnbind("IsL0Element");
myUnbind("IsLieElement");
myUnbind("IsLieEndo");
Reread(myFilePath("DD.g"));
Reread(myFilePath("lie0.g"));
Reread(myFilePath("lie.g"));
myUnbind("IsF4GroupElement");
Reread(myFilePath("group.g"));
Read(myFilePath("user_vars.g"));