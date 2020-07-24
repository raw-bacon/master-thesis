getCanonicalQuotientGroupOfOneSetOfObviousVisibleGenerators := function(code)
	local minimalNumber, generatingSetsOfArcs, setArcs, generatingSet, generatingSymbols, letters, free, gens, rels, gen;
	minimalNumber := minimalNumberOfObviousVisibleGenerators(code);
	setArcs := arcs(code);
	generatingSetsOfArcs := Filtered(Combinations(setArcs), sub -> Size(sub) = minimalNumber and isObviousVisibleGeneratingSet(sub, code));
	letters := namesOfArcs(setArcs);
	for generatingSet in generatingSetsOfArcs do
		generatingSymbols := List(generatingSet, arc -> letters[indexOf(arc, code)]);
		free := FreeGroup(generatingSymbols);
		gens := GeneratorsOfGroup(free);
		rels := getGroupRelatorsWithRespectToGeneratingSet(generatingSet, code, free);
		return free/rels;
	od;
	return fail;
end;



#<group> is an FpGroup, returns whether when mapping GeneratorsOfGroup(<group>) to
#S_<n> via <transpositions>, the map extends to the whole of <group>.
isSymmetricColoring := function(group, n, transpositions)
	local s_n, free, gens, homomorphism, rels, e;
	s_n := SymmetricGroup(n);
	
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);
	
	if Length(gens) <> Length(transpositions) then
		Print("<tuple> is of invalid length (", Length(transpositions), " instead of ", Length(gens), ")\n");
		return fail;
	fi;
	
	homomorphism := GroupHomomorphismByImagesNC(free, s_n, gens, transpositions);
	rels := RelatorsOfFpGroup(group);
	
	return(ForAll(rels, rel -> Image(homomorphism,rel) = ()));
end;



listSymmetricColoringsOfOrder := function(code, n)
	local group, free, gens, transpositions, possibleColorings, count, countProper, images;
	group := getCanonicalQuotientGroupOfOneSetOfObviousVisibleGenerators(code);
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);	
	
	transpositions := List(Filtered(Tuples([1 .. n], 2), tuple -> tuple[1] < tuple[2]), tuple -> (tuple[1], tuple[2]));
	possibleColorings := Tuples(transpositions, Length(gens));
	
	count := 0;
	countProper := 0;
	images := [];
	for transpositions in possibleColorings do
		if isSymmetricColoring(group,n,transpositions) then
			count := count + 1;
			Add(images, transpositions);
			if Size(Group(transpositions)) = Factorial(n) then
				countProper := countProper + 1;
			fi;
		fi;
	od;
	
	Print("Found ", count, " distinct colorings. ", countProper, " of them were proper.\n");
	return images;
end;

conjugation := function(list, g)
	return g*list*g^-1;
end;

countOrbitsOfOrder := function(code, n)
	local perms, count;
	perms := listSymmetricColoringsOfOrder(code, n);
	count := Size(OrbitsDomain(SymmetricGroup(n), perms, conjugation));
	Print("The number of orbits is ", count, "\n");
end;


listOrbitsOfOrder := function(code, n)
	local perms;
	perms := listSymmetricColoringsOfOrder(code, n);
	return OrbitsDomain(SymmetricGroup(n), perms, conjugation);
end;