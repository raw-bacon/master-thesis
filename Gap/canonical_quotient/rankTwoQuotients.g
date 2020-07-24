getGroupRelatorsWithRespectToGeneratingSet := function(generatingSet, code, free)
	local allArcs, crossing, setCrossings, gen, gens, arcsExpressed, rels, arc, count, maximum, longestRelator;
	allArcs := arcs(code);
	setCrossings := crossings(code);
	gens := GeneratorsOfGroup(free);
	arcsExpressed := List(allArcs, arc -> fail);
	rels := [];
	count := 1;
	for arc in generatingSet do
		arcsExpressed[indexOf(arc, code)] := gens[count];
		count := count + 1;
	od;
	
	for gen in gens do
		Add(rels, [gen^2, Identity(free)]);
	od;
	
	while setCrossings <> [] do
		for crossing in setCrossings do
			if arcsExpressed[indexOf(crossing[1], code)] <> fail and (arcsExpressed[indexOf(crossing[2], code)] <> fail 
																   or arcsExpressed[indexOf(crossing[3], code)] <> fail) then
				if arcsExpressed[indexOf(crossing[2], code)] = fail then
					arcsExpressed[indexOf(crossing[2], code)] := arcsExpressed[indexOf(crossing[1], code)] * arcsExpressed[indexOf(crossing[3], code)]
																										   * arcsExpressed[indexOf(crossing[1], code)];
					Unbind(setCrossings[Position(setCrossings, crossing)]);
				elif arcsExpressed[indexOf(crossing[3], code)] = fail then
					arcsExpressed[indexOf(crossing[3], code)] := arcsExpressed[indexOf(crossing[1], code)] * arcsExpressed[indexOf(crossing[2], code)]
																										   * arcsExpressed[indexOf(crossing[1], code)];
				else
					Add(rels, [arcsExpressed[indexOf(crossing[1], code)]*arcsExpressed[indexOf(crossing[2], code)]*
							   arcsExpressed[indexOf(crossing[1], code)]*arcsExpressed[indexOf(crossing[3], code)],
							   Identity(free)]);
					Unbind(setCrossings[Position(setCrossings, crossing)]);
				fi;
			fi;
		od;
		setCrossings := Set(setCrossings);
	od;
	
	#the longest relator is not necessary
	maximum := Maximum(List(rels, rel -> Length(rel[1])));
	longestRelator := Filtered(rels, rel -> Length(rel[1]) = maximum)[1];
	Unbind(rels[Position(rels, longestRelator)]);
	return Set(rels);
end;

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

# <imagesOfGenerators> contain the images of the second , third ... last generators
# as elements of the free group over which <group> is presented
isRankTwoQuotient := function(group, n, tuple)
	#LOCAL blablabla
	sigma := ();
	tau := ();
	if n mod 2 = 0 then
		k := Int(n / 2);
		for l in [1 .. k] do
			sigma := sigma * (l, 2*k - l + 1);
		od;
		for l in [1 .. k - 1] do
			tau := tau * (l, 2*k - l);
		od;
	else
		k := Int((n-1)/2);
		for l in [1 .. k] do
			sigma := sigma * (l, 2*k - l + 2);
			tau := tau * (l, 2*k - l + 1);
		od;
	fi;
	d_n := Group(sigma, tau);
	
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);
	if Length(gens) <> Length(tuple) then
		Print("<tuple> is of invalid length. \n");
		return fail;
	fi;
	
	images := [];
	for i in [1 .. Length(tuple)] do
		images[i] := (sigma*tau)^tuple[i] * sigma;
	od;
	
	homomorphism := GroupHomomorphismByImagesNC(free, d_n, gens, images);
	rels := RelatorsOfFpGroup(group);
	
	return(ForAll(rels, rel -> rel in Kernel(homomorphism)));
end;


listRankTwoQuotients := function(code)
	local free, gens, rels, max, n, images, i, j, tuples, tuple, numbers, primes, k, group;
	group := getCanonicalQuotientGroupOfOneSetOfObviousVisibleGenerators(code);
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);
	rels := RelatorsOfFpGroup(group);
	max := Maximum(List(rels, rel -> Length(rel)));
	
	primes := [];
	numbers := [1 .. max];
	Unbind(numbers[1]);
	for n in numbers do
		Add(primes, n);
		k := 1;
		while k*n <= max do
			Unbind(numbers[k*n]);
			k := k + 1;
		od;
	od;
		
	for n in primes do
		tuples := Tuples([0 .. n - 1], Length(gens) - 1);
		for tuple in tuples do
			tuple := Concatenation([0], tuple);
			if Size(Set(tuple)) > 1 then
				if isRankTwoQuotient(group,n,tuple) then
					Print(group, " has a quotient D_", n, " with images ", tuple, "\n");
				fi;
			fi;
		od;
		Print("did ", n, " / ", primes[Length(primes)], "\n");
	od;
end;


listRankTwoQuotientsOfOrder := function(code, n)
	group := getCanonicalQuotientGroupOfOneSetOfObviousVisibleGenerators(code);
	free := FreeGroupOfFpGroup(group);
	gens := GeneratorsOfGroup(free);
	rels := RelatorsOfFpGroup(group);
	
	tuples := Tuples([0 .. n - 1], Length(gens) - 1);
	for tuple in tuples do
		tuple := Concatenation([0], tuple);
		if Size(Set(tuple)) > 1 then
			if isRankTwoQuotient(group,n,tuple) then
				Print(group, " has a quotient D_", n, " with images ", tuple, "\n");
			fi;
		fi;
	od;
end;


listAllRankTwoQuotients := function(code)
	local quotients, group;
	quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
	
	for group in quotients do
		Print("Considering ", group, " ... \n");
		listRankTwoQuotients(group);
	od;
end;