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

#returns the relators of a gauss code
getRelators := function(f, code)
	local setArcs, gens, rels, crossing, over, under1, under2, gen;
	setArcs := arcs(code);
	gens := GeneratorsOfGroup(f);
	rels := [];
	
	for crossing in crossings(code) do
		over := gens[Position(setArcs, crossing[1])];
		under1 := gens[Position(setArcs, crossing[2])];
		under2 := gens[Position(setArcs, crossing[3])];
		
		Add(rels, over*under1*over*under2);
	od;
	
	for gen in gens do Add(rels, gen^2); od;
	return rels;
end;

#computes the canonical quotient of a gauss code, defined to be the quotient
#of the fundamental group by the square of one of its meridians. as implemented
#here, it does not first compute the wirtinger presentation.
canonicalQuotient := function(code)
	local setArcs, crossing, gen, f, gens, rels, over, under1, under2;
	setArcs := arcs(code);
	f:= FreeGroup(namesOfArcs(setArcs));
	rels := getRelators(f, code);
	return f/rels;
end;




size := code -> Size(canonicalQuotient(code));
description := code -> StructureDescription(canonicalQuotient(code):nice);


#returns a list of generators of a given group of known finite order
identifyReasonableSetOfGenerators := function(cq)
	local gens, list, g, order, bestGenerator, bestOrder, gen;
	gens := GeneratorsOfGroup(cq);
	
	#computes permutation representation to make run faster
	Size(cq);	
	
	list := [];
	g := Group(gens[1]);
	order := 1;
	
	bestGenerator := gens[1];
	bestOrder := 1;
	
	while order < Order(cq) do
		for gen in gens do
			g := Group(Concatenation(list, [gen]));
			order := Order(g);
			if bestOrder < order then
				bestGenerator := gen;
				bestOrder := Order(g);
			fi;
		od;
		Add(list, bestGenerator);
	od;
	
	return Set(list);
end;