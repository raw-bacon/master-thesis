#finds finite coxeter quotients of rank 3

#depends on canonicalQuotientFromGausscode.g
Read("../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/canonicalQuotientFromGaussCode.g");

#depends on
Read("../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/coxeterGroupFromGroupPresentation.g");

finiteCoxeterQuotients := function(list)
	local code, cq, gens, listArcs, bridges, bridgePositions, viableGenerators, gen, cosetTable;
	for code in list do
		cq := canonicalQuotient(code);
		gens := GeneratorsOfGroup(cq);
		listArcs := arcs(code);
		bridges := Filtered(listArcs, x -> Length(x) > 2);
		bridgePositions := List([1 .. Length(bridges)], i -> Position(listArcs, bridges[i]));
		viableGenerators := gens{bridgePositions};
		
		#now guesswork begins
		for gen1 in viableGenerators do
			for gen2 in viableGenerators do
				for gen3 in viableGenerators do
					
					
					if gen1 <> gen2 and gen1 <> gen3 and gen2 <> gen3 then
						#try whether they generate?
					fi;
					
					#something like this? (would check whether cq is computably finite)
					#cosetTable := TryCosetTableInWholeGroup(TrivialSubgroup(cq):silent);
					
				od;
			od;
		od;
	od;
end;