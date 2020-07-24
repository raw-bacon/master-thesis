#checks whether it's on the list of finite coxeter groups
#only then computes the order, otherwise returns infinity
orderOfCoxeterGroup := function(order12, order13, order23)
	local orders, finite, f;
	orders := [order12, order13, order23];
	Sort(orders);
	finite := false;
	if orders[1] = 2 then
		if orders[2] = 2 then finite := true;
		elif orders[2] = 3 then
			if orders[3] <= 5 then finite := true; fi;
		fi;
	fi;
	
	if finite then
		f := FreeGroup("a","b","c");
		return Order(f/[((f.1)*(f.2))^order12, 
						((f.1)*(f.3))^order13, 
						((f.2)*(f.3))^order23,
						(f.1)^2, (f.2)^2, (f.3)^2]);
	fi;
	return infinity;
end;


isCoxeter := function(g) 
	local gens;
	
	gens := GeneratorsOfGroup(g);
	
	if Length(gens) < 3 then return false; fi;
	return Order(g) = orderOfCoxeterGroup(Order(gens[1]*gens[2]),
										  Order(gens[1]*gens[3]),
										  Order(gens[2]*gens[3]));
end;


#changes the names of a list of groups to Cox(n,k,l)										 
nameListOfCoxeterGroups := function(list)
	local name, g, orders, gens;
	for g in list do
		gens := GeneratorsOfGroup(g);
		orders := [, , ];
		name := Concatenation("Cox(",
							  String(Order(gens[1]*gens[2])),",",
							  String(Order(gens[1]*gens[3])),",",
							  String(Order(gens[2]*gens[3])),
							  ")");
		SetName(g, name);
	od;
end;


#helper method for fixed generator coxeter quotient finding function
divisors := n -> Filtered(DivisorsInt(n), x -> not (x = 1 or x = n));


#returns coxeter quotients with fixed generators
coxeterQuotients := function(g)
	local list, h, n, divs, normal, hom, gens;
	list := [];
	gens := GeneratorsOfGroup(g);
	if isCoxeter(g) then Add(list, g);
	elif Length(gens) > 2 then
		divs := divisors(Order(gens[1]*gens[2]));
		for n in divs do
			normal := NormalClosure(g, Subgroup(g, [(gens[1]*gens[2])^n]));
			hom := NaturalHomomorphismByNormalSubgroup(g, normal);
			h := ImagesSource(hom);
			if not IsTrivial(h) then
				Append(list, coxeterQuotients(h));
			fi;
		od;
		
		divs := divisors(Order(gens[1]*gens[3]));
		for n in divs do
			normal := NormalClosure(g, Subgroup(g, [(gens[1]*gens[3])^n]));
			hom := NaturalHomomorphismByNormalSubgroup(g, normal);
			h := ImagesSource(hom);
			if not IsTrivial(h) then
				Append(list, coxeterQuotients(h));
			fi;
		od;
		
		divs := divisors(Order(gens[2]*gens[3]));
		for n in divs do
			normal := NormalClosure(g, Subgroup(g, [(gens[2]*gens[3])^n]));
			hom := NaturalHomomorphismByNormalSubgroup(g, normal);
			h := ImagesSource(hom);
			if not IsTrivial(h) then
				Append(list, coxeterQuotients(h));
			fi;
		od;
	fi;
	nameListOfCoxeterGroups(list); #inefficient - is done multiple times.
	return list;
end;

#should be called if g is not known to be finite.
cautiousCoxeterQuotients := function(g)
	local list, h;
	list := [];
	
	h := g/[(g.1*g.2)^2];
	Append(list, coxeterQuotients(h));
	
	h := g/[(g.1*g.3)^2];
	Append(list, coxeterQuotients(h));
	
	h := g/[(g.2*g.3)^2];
	Append(list, coxeterQuotients(h));
	
	return list;
end;

#desperately looks for ALL coxeter quotients, even with other
#generating meridians
allCoxeterQuotients := function(g)
	local meridians, list, tmp, order, x, y, z, numberOfMeridians, count;
	order := Order(g);
	
	#debug
	Print("the canonical quotient has order ", order, ".\n");
	#end
	
	meridians := g.1^g;
	numberOfMeridians := Size(meridians);
	
	
	#debug
	Print("there are ", numberOfMeridians, " meridians.\n");
	#end
	
	count := 0;
	list := [];
	for x in meridians do
		for y in meridians do
			for z in meridians do
				tmp := Group(x,y,z);
				if Order(tmp) = order then
					Append(list, coxeterQuotients(tmp));
					if list <> [] then 
						Print(x, ", ", y, ", ", z, " were successful.\n");
					fi;
				fi;
			od;
		od;
	od;
end;