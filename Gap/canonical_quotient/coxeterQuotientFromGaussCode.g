#depends on canonicalQuotientFromGaussCode.g
#depends on coxeterQuotientFromGroupPresentation.g
Read("../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/canonicalQuotientFromGaussCode.g");
Read("../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/coxeterGroupFromGroupPresentation.g");

tryToFindThreeGeneratorCoxeterQuotient := function(code)
	local cq, list;
	cq := GroupWithGenerators(identifyReasonableSetOfGenerators(canonicalQuotient(code)));
	list := allCoxeterQuotients(cq);
	if list = [] then return "no quotient found";
	else return list[1]; fi;
end;

#tries to compute the size of a canonical quotient (kind of in the wrong file)
extractAsMuchAsYouCan := function(list)
	local code, success, foundList, cq, cosetTable;
	success := true;
	foundList := [];
	for code in list do
		#try to find out whether coset enumeration will go into a braik loop
		cq := canonicalQuotient(code);
		cosetTable := TryCosetTableInWholeGroup(TrivialSubgroup(cq):silent);
		
		if cosetTable <> fail then
			Add(foundList, size(code));
			Print("FOUND SOMETHING FOR ", code, "\n");
		else 
			Add(foundList, "?");
			Print("FOUND NOTHING \n");
		fi;
		
		success := true;
	od;
	return foundList;
end;