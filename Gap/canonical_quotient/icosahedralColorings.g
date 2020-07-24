

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
isIcosahedralColoring := function(group, cox, transpositions)
	local s_n, free, gens, homomorphism, rels, e;
	
	
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);
	e := Identity(cox);
	
	if Length(gens) <> Length(tuple) then
		Print("<tuple> is of invalid length. \n");
		return fail;
	fi;
	
	homomorphism := GroupHomomorphismByImagesNC(free, cox, gens, transpositions);
	rels := RelatorsOfFpGroup(group);
	
	return(ForAll(rels, rel -> Image(homomorphism,rel) = e));
end;



listIcosahedralColoringsOfOrder := function(code, cox)
	local group, free, gens, transpositions, possibleColorings, count, countProper, images, gensCox, reflections;
	group := getCanonicalQuotientGroupOfOneSetOfObviousVisibleGenerators(code);
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);	
	
	gensCox := GeneratorsOfGroup(cox);
	reflections := gensCox[1]^cox;
	possibleColorings := Tuples(reflections, Length(gens));
	
	count := 0;
	countProper := 0;
	images := [];
	for transpositions in possibleColorings do
		if isIcosahedralColoring(group,cox,transpositions) then
			count := count + 1;
			Add(images, transpositions);
			if Size(Group(transpositions)) = 120 then
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

cox235 := function()
	local free, gens, a,b,c, group;
	free := FreeGroup("a","b","c");
	gens := GeneratorsOfGroup(free);
	a := gens[1];
	b := gens[2];
	c := gens[3];
	group := free/[a^2,b^2,c^2,(a*b)^3,(a*c)^2,(b*c)^5];
	Size(group);
	return group;
end;

countIcosahedralOrbits := function(code)
	local perms, count, cox;
	cox := cox235();
	perms := listIcosahedralColoringsOfOrder(code, cox);
	count := Size(OrbitsDomain(cox, perms, conjugation));
	Print("The number of orbits is ", count, "\n");
end;