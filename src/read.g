myUnbind := function(s)
	if IsBoundGlobal(s) then
		MakeReadWriteGlobal(s);
		UnbindGlobal(s);
	fi;
end;

# Reread("./F4-5Grading.g");
Reread("./F4-roots.g");
Reread("./helper.g");
Reread("./conic.g");
myUnbind("IsCubicElement");
Reread("./cubic.g");
myUnbind("IsBrownElement");
Reread("./brown.g");
myUnbind("IsDDElement");
myUnbind("IsL0Element");
myUnbind("IsLieElement");
Reread("./lie0.g");
Reread("./lie.g");
myUnbind("IsF4GroupElement");
Reread("./group.g");
Read("./user_vars.g");