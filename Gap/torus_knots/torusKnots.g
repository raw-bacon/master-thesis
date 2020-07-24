# gets the desired monoid with n generators
free2TorsionMonoid := function(n)
	local f, letters, indexOfSmallA, gens, rels;
	indexOfSmallA := 97;
	letters := List([indexOfSmallA .. n + indexOfSmallA - 1], x->[CharInt(x)]);
	f := FreeMonoid(letters);
	gens := GeneratorsOfMonoid(f);
	rels := List(gens, x -> [x^2, Identity(f)]);
	return f/rels;
end;


# computes the relations obtained from a torus twist sigma_1 sigma_2 ... sigma_n-1
twist := function(list, rws)
	#TODO: generalize
	local a, b, c;
	a := list[1];
	b := list[2];
	c := list[3];
	return [ReducedForm(rws, a*b*a), 
			ReducedForm(rws, a*c*a), 
			ReducedForm(rws, a)];
end;

#todo: generalize for p != 3
#f is the free monoid on 3 generators modulo generators^2
torusRels1 := function(p,q, fModTwo)
	local f, gens, rels, a,b,c,k;
	
	if p <> 3 then return fail; fi;
	gens := GeneratorsOfMonoid(fModTwo);
	a := UnderlyingElement(gens[1]);
	b := UnderlyingElement(gens[2]);
	c := UnderlyingElement(gens[3]);
	rels := [];
	k := (q - (q mod 3))/3;
	if q mod 3 =0 then
		rels := [(c*b*a)^(k-1)*c*b*a*b*c*(a*b*c)^(k-1)*a, 
				 (c*b*a)^(k-1)*c*b*c*(a*b*c)^(k-1)*a*b*a];
	elif q mod 3 = 1 then
		rels := [(c*b*a)^(k-1)*c*b*a*b*a*b*c*(a*b*c)^(k-1)*a,
				 (c*b*a)^k*b*c*b*(a*b*c)^k*a*b*a];
	elif q mod 3 = 2 then
		rels := [(c*b*a)^k*c*(a*b*c)^k*a,
				 (c*b*a)^k*b*a*b*(a*b*c)^k*a*b*a];
	fi;
	return rels;
end;


# list contains the meridians associated to the bottommost lines in the braid representation
torusRels := function(p,q,fModTwo, list)
	local gens, tmpList, rels, n, a, b, c, rws;
	if p <> 3 then return fail; fi;
	
	tmpList := List(list, x -> UnderlyingElement(x));
	rws := KnuthBendixRewritingSystem(fModTwo);
	
	for n in [1 .. q] do
		tmpList := twist(tmpList, rws);
	od;
	
	rels := [];
	Add(rels, ReducedForm(rws, tmpList[1]*UnderlyingElement(list[1])));
	Add(rels, ReducedForm(rws, tmpList[2]*UnderlyingElement(list[2])));
	return rels;
end;


#returns a free product of 3 factors of Z/2
free3 := function()
	local f, gens, e;
	f := FreeMonoid("a","b","c");
	gens := GeneratorsOfMonoid(f);
	e := gens[1]^0;
	return f/[[gens[1]^2, e], [gens[2]^2, e], [gens[3]^2, e]];
end;


#returns a rewrite system solving the word problem for the coxeter group on three generators
coxeterRws := function(ab,ac,bc, fModTwo)
	local gens, rels, cox, e, k, n, a,b,c;
	gens := GeneratorsOfMonoid(fModTwo);
	e := gens[1]^0;
	a := gens[1];
	b := gens[2];
	c := gens[3];
	rels := [];
	
	if ab mod 2 = 0 then
		n := ab/2;
		Add(rels, [(a*b)^n, (b*a)^n]);
	elif ab mod 2 = 1 then
		n := (ab-1)/2;
		Add(rels, [(a*b)^n*a, (b*a)^n*b]);
	fi;
	
	if ac mod 2 = 0 then
		n := ac/2;
		Add(rels, [(a*c)^n, (c*a)^n]);
	elif ac mod 2 = 1 then
		n := (ac-1)/2;
		Add(rels, [(a*c)^n*a, (c*a)^n*c]);
	fi;
	
	if bc mod 2 = 0 then
		n := bc/2;
		Add(rels, [(b*c)^n, (c*b)^n]);
	elif bc mod 2 = 1 then
		n := (bc-1)/2;
		Add(rels, [(b*c)^n*b, (c*b)^n*c]);
	fi;
	
	cox := fModTwo/rels;
	k := KnuthBendixRewritingSystem(cox);
	
	#MakeConfluent(k);
	return k;
end;


#tries to find a coxeter quotient
#f is a free product of three Z/2's
coxQuotient := function(f, rels)
	local rel1, rel2, ab, ac, bc, min, rws, quotients, e;
	rel1 := rels[1];
	rel2 := rels[2];
	e := UnderlyingElement(One(f));
	min := Minimum(Length(rel1), Length(rel2));
	quotients := [];
	for ab in [2..min] do
		for ac in [2..min] do
			for bc in [2..min] do
				rws := coxeterRws(ab,ac,bc, f);
				if ReducedForm(rws, rel1) = e and ReducedForm(rws, rel2) = e then
					Add(quotients, [ab,ac,bc]);
				fi;
			od;
		od;
	od;
	return quotients;
end;

#runs
run := function(n)
	local quotients, q, f, rels;
	f := free3();
	a := GeneratorsOfMonoid(f)[1];
	b := GeneratorsOfMonoid(f)[2];
	c := GeneratorsOfMonoid(f)[3];
	for q in [4 .. n] do
		rels := torusRels(3,q,f, [a,a*b*a,a*b*c*b*a]);
		Print("T(3,",q,"): ", coxQuotient(f, rels), "\n");
	od;
end;
