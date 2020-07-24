#code should be a list with non-repeating integers
arcs := function(code)
	local list, listOfVertices, startOfArc, endOfArc, firstNegative, length, i;
	length := Length(code);
	list := [];
	
	startOfArc := 0;
	endOfArc := 0;
	firstNegative := 0;
	for i in [1 .. length] do
		if code[i] < 0 then 
			endOfArc := i;
			
			#in first loop don't do this
			if firstNegative > 0 then Add(list, code{[startOfArc .. endOfArc]}); fi;
			
			#first loop over
			if firstNegative = 0 then firstNegative := i; fi;		
			startOfArc := i;
		fi;
	od;
	#final arc
	Add(list, Concatenation(code{[startOfArc .. length]}, code{[1 .. firstNegative]}));
	return Set(list);
end;

namesOfArcs := function(set)
	local indexOfSmallA;
	indexOfSmallA := 97;
	return List([indexOfSmallA .. Size(set) + indexOfSmallA - 1], x->[CharInt(x)]);
end;

indexOf := function(arc, code)
	return Position(arcs(code), arc);
end;

#returns the set of crossings of a gauss code.
#a crossing is a triple of arcs. the first arc
#is called OVER, and the two subsequent ones
#are called under.
crossings := function(code)
	local i, list, setArcs, ixs, over, under1, under2, arc;
	ixs := [1 ..Maximum(code)];
	setArcs := arcs(code);
	
	over := [];
	under1 := [];
	under2 := [];
	list := [];
	
	for i in ixs do
		for arc in setArcs do
			if i in arc then over := arc; fi;
			if -i in arc then
				if under1 = [] then under1 := arc;
				else under2 := arc; fi;
			fi;
		od;
		Add(list, [over, under1, under2]);
		over:=[];
		under1:=[];
	od;
	return list;
end;


isObviousVisibleGeneratingSet := function(inputArcs, code)
	local allArcs, setCrossings, generatedArcs, didSomething, crossing;
	allArcs := arcs(code);
	setCrossings := crossings(code);
	generatedArcs := ShallowCopy(inputArcs);
	
	didSomething := true;
	while didSomething do
		didSomething := false;
		for crossing in setCrossings do
			if crossing[1] in generatedArcs and (crossing[2] in generatedArcs or crossing[3] in generatedArcs) 
											and not (crossing[2] in generatedArcs and crossing[3] in generatedArcs) then
				didSomething := true;
				if crossing[2] in generatedArcs then Add(generatedArcs, crossing[3]);
				else Add(generatedArcs, crossing[2]); fi;
				
			fi;
		od;
	od;
	
	return allArcs = Set(generatedArcs);
end;


minimalNumberOfObviousVisibleGenerators := function(code)
	local setArcs, powerSet, n, subset;
	setArcs := arcs(code);
	powerSet := Combinations(setArcs);
	
	for n in [1 .. Length(setArcs)] do
		for subset in Filtered(powerSet, sub -> Size(sub) = n) do
			if isObviousVisibleGeneratingSet(subset, code) then return n; fi;
		od;
	od;
	return fail;
end;

getRelatorsWithRespectToGeneratingSet := function(generatingSet, code, free)
	local rws,allArcs, crossing, setCrossings, gen, gens, arcsExpressed, rels, arc, count, maximum, longestRelator;
	allArcs := arcs(code);
	setCrossings := crossings(code);
	gens := GeneratorsOfMonoid(free);
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
	
	rws := KnuthBendixRewritingSystem(free/rels);
	
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
					Add(rels, [ReducedForm(rws,arcsExpressed[indexOf(crossing[1], code)]*arcsExpressed[indexOf(crossing[2], code)]*
							   arcsExpressed[indexOf(crossing[1], code)]*arcsExpressed[indexOf(crossing[3], code)]),
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


#can be reused
getCanonicalQuotientsOfAllObviousVisibleGenerators := function(code)
	local minimalNumber, generatingSetsOfArcs, setArcs, generatingSet, generatingSymbols, letters, free, gens, rels, gen, quotients;
	minimalNumber := minimalNumberOfObviousVisibleGenerators(code);
	setArcs := arcs(code);
	generatingSetsOfArcs := Filtered(Combinations(setArcs), sub -> Size(sub) = minimalNumber and isObviousVisibleGeneratingSet(sub, code));
	letters := namesOfArcs(setArcs);
	quotients := [];
	for generatingSet in generatingSetsOfArcs do
		generatingSymbols := List(generatingSet, arc -> letters[indexOf(arc, code)]);
		free := FreeMonoid(generatingSymbols);
		gens := GeneratorsOfMonoid(free);
		rels := getRelatorsWithRespectToGeneratingSet(generatingSet, code, free);
		Add(quotients, free/rels);
	od;
	return quotients;
end;


isCoxeterQuotient := function(coxeterMatrix, canonicalQuotient)
	local free, gens, e, rels, row, col, m, n, a, b, cox, rws, relationsOfCanonicalQuotient;
	free := FreeMonoidOfFpMonoid(canonicalQuotient);
	gens := GeneratorsOfMonoid(free);
	e := Identity(free);
	rels := [];
	
	for row in [1 .. Size(coxeterMatrix)] do
		a := gens[row];
		Add(rels, [a^2, e]);
	od;
	
	for row in [1 .. Size(coxeterMatrix)] do
		for col in [row + 1 .. Size(coxeterMatrix)] do
			m := coxeterMatrix[row][col];
			if m <> infinity then
				a := gens[row];
				b := gens[col];
				if m mod 2 = 0 then
					n := m/2;
					Add(rels, [(a*b)^n, (b*a)^n]);
				else
					n := (m-1)/2;
					Add(rels, [(a*b)^n*a, (b*a)^n*b]);
				fi;
			fi;
		od;
	od;
	
	cox := free/rels;
	rws := KnuthBendixRewritingSystem(cox);
	
	
	relationsOfCanonicalQuotient := List(RelationsOfFpMonoid(canonicalQuotient), rel -> rel[1]);
	return ForAll(relationsOfCanonicalQuotient, rel -> ReducedForm(rws, rel) = e);
end;


#returns true if it is the trivial group
isTrivialCoxeterMatrix := function(matrix)
	local equalGenerators, i, j, k, equals;
	equalGenerators := List([1 .. Length(matrix)], x -> [x]);
	
	for i in [1 .. Length(matrix)] do
		for j in [1 .. Length(matrix)] do
			if matrix[i][j] = 1 then
				AddSet(equalGenerators[j], i);
				AddSet(equalGenerators[i], j);
			fi;
		od;
	od;
	
	for i in [1 .. Length(matrix)] do
		for j in [1 .. Length(matrix)] do
			for k in [1 .. Length(matrix)] do
				if i in equalGenerators[j] and i in equalGenerators[k] then
					AddSet(equalGenerators[i], j);
					AddSet(equalGenerators[i], k);
					
					AddSet(equalGenerators[j], i);
					AddSet(equalGenerators[j], k);
					
					AddSet(equalGenerators[k], i);
					AddSet(equalGenerators[k], j);
				fi;
			od;
		od;
	od;
	
	if equalGenerators[1] = [1 .. Length(matrix)] then
		return true;
	fi;
	
	for equals in equalGenerators do
		for i in equals do
			for j in equals do
				if matrix[i][j] <> 1 then
					return true;
				fi;
				for k in [1 .. Length(matrix)] do
					if matrix[i][k] <> matrix[j][k] then
						return true;
					fi;
				od;
			od;
		od;
	od;
	
	return false;
end;


next := function(list, max)
	local length, primes, numbers, n, k;	
	
	primes := [1];
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
	IsSet(primes);
	
	max := primes[Length(primes)];
	
	length := Length(list);
	list := ShallowCopy(list);
	if list[1] < max and list[1] < infinity then
		#next prime
		list[1] := primes[Position(primes, list[1]) + 1];
	elif list[1] = max then
		list[1] := infinity;
	else
		list := Concatenation([1], next(list{[2..length]}, max));
	fi;
	return list;
end;

allPrimeCoxeterMatrices := function(size, max)
	local list, coxeterMatrices, matrix, row, count, col;
	list := List([1 .. size*(size-1)/2], n -> 1);
	coxeterMatrices := [];
	while list <> List([1 .. size*(size-1)/2], n -> infinity) do
		matrix := [];
		for row in [1 .. size] do
			matrix[row] := [];
			matrix[row][row] := 1;
		od;
		
		count := 1;
		for row in [1 .. size] do
			for col in [row + 1 .. size] do
				matrix[row][col] := list[count];
				matrix[col][row] := list[count];
				count := count + 1;
			od;
		od;
		if not isTrivialCoxeterMatrix(matrix) then
			Add(coxeterMatrices, matrix);
		fi;
		list := next(list, max);
	od;
	SortBy(coxeterMatrices, matrix -> Maximum(List(matrix, row -> Maximum(row))));
	return coxeterMatrices;
end;


#todo: make work for coxeter matrices with ones
multiplesOf := function(matrix, max)
	local multiples, didSomething, row, col, k, newMultiple, equalGenerators, eq1, eq2, i, j;
	multiples := [];
	didSomething := true;
	
	
	equalGenerators := List([1 .. Length(matrix)], x -> [x]);
	
	for i in [1 .. Length(matrix)] do
		for j in [1 .. Length(matrix)] do
			if matrix[i][j] = 1 then
				AddSet(equalGenerators[j], i);
				AddSet(equalGenerators[i], j);
			fi;
		od;
	od;
	
	
	for i in [1 .. Length(matrix)] do
		for j in [1 .. Length(matrix)] do
			for k in [1 .. Length(matrix)] do
				if i in equalGenerators[j] and i in equalGenerators[k] then
					AddSet(equalGenerators[i], j);
					AddSet(equalGenerators[i], k);
					
					AddSet(equalGenerators[j], i);
					AddSet(equalGenerators[j], k);
					
					AddSet(equalGenerators[k], i);
					AddSet(equalGenerators[k], j);
				fi;
			od;
		od;
	od;
	
	
	
	for row in [1 .. Size(matrix)] do
		for col in [row + 1 .. Size(matrix)] do
			k := 2;
			while k * matrix[row][col] <= max do
				newMultiple := StructuralCopy(matrix);
				for eq1 in equalGenerators[row] do
					for eq2 in equalGenerators[col] do
						newMultiple[eq1][eq2] := k*matrix[row][col];
						newMultiple[eq2][eq1] := k*matrix[row][col];
					od;
				od;
				
				
				if not newMultiple in multiples then
					AddSet(multiples, newMultiple);
					didSomething := true;
				fi;
				k := k + 1;
			od;
			newMultiple := StructuralCopy(matrix);
			if newMultiple[row][col] < infinity then 
				for eq1 in equalGenerators[row] do
					for eq2 in equalGenerators[col] do
						newMultiple[eq1][eq2] := infinity;
						newMultiple[eq2][eq1] := infinity;
					od;
				od;
				AddSet(multiples, newMultiple);
			fi;
		od;
	od;
	return Set(multiples);
end;



findAllCoxeterQuotientsWithRespectToOneGeneratingSet := function(canonicalQuotient)
	local rels, max, coxeterMatrices, coxeterQuotients, matrix, lastEntry, otherMatrix, row, col, multiple;
	rels := List(RelationsOfFpMonoid(canonicalQuotient), rel -> rel[1]);
	max := Maximum(List(rels, rel -> Length(rel)));
	Print(" with a maximum relation length of ", max, "\n");
	coxeterMatrices := allPrimeCoxeterMatrices(Length(GeneratorsOfMonoid(canonicalQuotient)), max);
	coxeterQuotients := [];
	for matrix in coxeterMatrices do
		if isCoxeterQuotient(matrix, canonicalQuotient) then
			AddSet(coxeterQuotients, matrix);
			Print("Found ", matrix, "\n");
			for matrix in multiplesOf(matrix, max) do
				if not matrix in coxeterMatrices and not isTrivialCoxeterMatrix(matrix) then
					Add(coxeterMatrices, matrix);
				fi;
			od;
		fi;
	od;
	return coxeterQuotients;
end;

findSmallCoxeterQuotientsWithRespectToOneGeneratingSet := function(canonicalQuotient, max)
	local rels, coxeterMatrices, coxeterQuotients, matrix, lastEntry, otherMatrix, row, col, multiple;
	rels := List(RelationsOfFpMonoid(canonicalQuotient), rel -> rel[1]);
	coxeterMatrices := allPrimeCoxeterMatrices(Length(GeneratorsOfMonoid(canonicalQuotient)), max);
	coxeterQuotients := [];
	for matrix in coxeterMatrices do
		if isCoxeterQuotient(matrix, canonicalQuotient) then
			AddSet(coxeterQuotients, matrix);
			Print("Found ", matrix, "\n");
			for matrix in multiplesOf(matrix, max) do
				if not matrix in coxeterMatrices then
					Add(coxeterMatrices, matrix);
				fi;
			od;
		fi;
	od;
	return coxeterQuotients;
end;



findAllObviousVisibleCoxeterQuotients := function(code)
	local quotients, coxeterQuotients, quotient, matrices;
	quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
	coxeterQuotients := [];
	for quotient in quotients do
		Print("Considering ", quotient);
		matrices := findAllCoxeterQuotientsWithRespectToOneGeneratingSet(quotient);
		Add(coxeterQuotients, [quotient, matrices]);
	od;
	return coxeterQuotients;
end;


#max should be small. this is the only way to handle bigger (>3-bridge or >11crossings) knots 
findSmallObviousVisibleCoxeterQuotients := function(code, max)
	local quotients, coxeterQuotients, quotient, matrices;
	quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
	coxeterQuotients := [];
	for quotient in quotients do
		matrices := findSmallCoxeterQuotientsWithRespectToOneGeneratingSet(quotient, max);
		Add(coxeterQuotients, [quotient, matrices]);
	od;
	return coxeterQuotients;
end;



#max should be small. this is the only way to handle bigger (>3-bridge or >11crossings) knots 
findSmallObviousVisibleCoxeterQuotients3Bridge := function(code, max)
	local quotients, coxeterQuotients, quotient, matrices, matrix, view, new;
	quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
	coxeterQuotients := [];
	for quotient in quotients do
		matrices := findSmallCoxeterQuotientsWithRespectToOneGeneratingSet(quotient, max);
		Add(coxeterQuotients, [quotient, matrices]);
	od;
	view := [];
	for quotient in coxeterQuotients do
		for matrix in quotient[2] do
			new := [matrix[1][2], matrix[1][3], matrix[2][3]];
			Sort(new);
			AddSet(view, new);
		od;
	od;
	Print("Found the quotients ", view, "\n");
end;






#TRASH FUNCTIONS AHEAD


#searches lists of gauss codes
findSmallObviousVisibleCoxeterQuotientsInList := function(codes, max)
	local quotients, coxeterQuotients, quotient, matrices, code, none;
	for code in codes do
		Print("Considering ", code, "\n");
		quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
		coxeterQuotients := [];
		none := true;
		for quotient in quotients do
			matrices := findSmallCoxeterQuotientsWithRespectToOneGeneratingSet(quotient, max);
			if matrices <> [] then
				none := false;
			fi;
		od;
		if not none then 
			Print("COUNTEREXAMPLE: ", code, "\n");
			return fail;
		fi;
	od;
	
	return coxeterQuotients;
end;


hasSmallObviousVisibleCoxeterQuotients := function(code, max)
	local quotients, coxeterQuotients, quotient, matrices;
	quotients := getCanonicalQuotientsOfAllObviousVisibleGenerators(code);
	coxeterQuotients := [];
	for quotient in quotients do
		matrices := findSmallCoxeterQuotientsWithRespectToOneGeneratingSet(quotient, max);
		if matrices <> [] then return true; fi;
	od;
	return false;
end;


confirmEveryDiagramHasSmallObviousCoxeterQuotient := function(codes, max)
	local code, quotients, coxeterQuotients, quotient, matrices;
	for code in codes do
		Print("Considering ", code, "\n");
		if not hasSmallObviousVisibleCoxeterQuotients(code, max) then
			Print("NO! Found one that doesn't admit one: ", code, "\n");
			return false;
		fi;
	od;
	Print("done. \n");
	return true;
end;