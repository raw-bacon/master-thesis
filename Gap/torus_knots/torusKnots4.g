#returns a free product of 3 factors of Z/2
free4 := function()
	local f, gens, e;
	f := FreeMonoid("a","b","c", "d");
	gens := GeneratorsOfMonoid(f);
	e := gens[1]^0;
	return f/[[gens[1]^2, e], [gens[2]^2, e], [gens[3]^2, e], [gens[4]^2,e]];
end;

# computes the relations obtained from a torus twist sigma_1 sigma_2 ... sigma_n-1
twist := function(list, rws)
	#TODO: generalize
	local a, b, c, d, i;
	a := list[1];
	b := list[2];
	c := list[3];
	d := list[4];
	return [ReducedForm(rws, a*b*a), 
			ReducedForm(rws, a*c*a), 
			ReducedForm(rws, a*d*a),
			ReducedForm(rws, a)];
end;

# list contains the meridians associated to the bottommost lines in the braid representation
torusRels := function(p,q,fModTwo, list)
	local gens, tmpList, rels, n, a, b, c, rws, i;
	if p <> 4 then return fail; fi;
	
	tmpList := List(list, x -> UnderlyingElement(x));
	rws := KnuthBendixRewritingSystem(fModTwo);
	
	for n in [1 .. q] do
		tmpList := twist(tmpList, rws);
	od;
	
	rels := [];
	for i in [1 .. Length(tmpList) - 1] do
		Add(rels, ReducedForm(rws, tmpList[i]*UnderlyingElement(list[i])));
	od;
	return rels;
end;

#returns a rewrite system solving the word problem for the coxeter group on three generators
coxeterRws := function(ab,ac,ad,bc,bd,cd, fModTwo)
	local gens, rels, cox, e, k, n, a,b,c,d;
	gens := GeneratorsOfMonoid(fModTwo);
	e := gens[1]^0;
	a := gens[1];
	b := gens[2];
	c := gens[3];
	d := gens[4];
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
	
	if ad mod 2 = 0 then
		n := ad/2;
		Add(rels, [(a*d)^n, (d*a)^n]);
	elif ad mod 2 = 1 then
		n := (ad-1)/2;
		Add(rels, [(a*d)^n*a, (d*a)^n*d]);
	fi;
	
	if bc mod 2 = 0 then
		n := bc/2;
		Add(rels, [(b*c)^n, (c*b)^n]);
	elif bc mod 2 = 1 then
		n := (bc-1)/2;
		Add(rels, [(b*c)^n*b, (c*b)^n*c]);
	fi;
	
	if bd mod 2 = 0 then
		n := bd/2;
		Add(rels, [(b*d)^n, (d*b)^n]);
	elif bd mod 2 = 1 then
		n := (bd-1)/2;
		Add(rels, [(b*d)^n*b, (d*b)^n*d]);
	fi;
	
	if cd mod 2 = 0 then
		n := cd/2;
		Add(rels, [(c*d)^n, (d*c)^n]);
	elif cd mod 2 = 1 then
		n := (cd-1)/2;
		Add(rels, [(c*d)^n*c, (d*c)^n*d]);
	fi;
	
	cox := fModTwo/rels;
	k := KnuthBendixRewritingSystem(cox);
	
	#MakeConfluent(k);
	return k;
end;

#tries to find a coxeter quotient
#f is a free product of four Z/2's
coxQuotient := function(f, rels)
	local rel1, rel2,rel3, ab, ac, ad, bc, bd, cd, min, rws, quotients, e;
	rel1 := rels[1];
	rel2 := rels[2];
	rel3 := rels[3];
	e := UnderlyingElement(One(f));
	min := Minimum(Length(rel1), Length(rel2), Length(rel3));
	quotients := [];
	for ab in [2..min] do
		for ac in [2..min] do
			for ad in [2..min] do
				for bc in [2..min] do
					for bd in [2..min] do
						for cd in [2..min] do
							rws := coxeterRws(ab,ac,ad,bc,bd,cd, f);
							if ReducedForm(rws, rel1) = e and ReducedForm(rws, rel2) = e and ReducedForm(rws, rel3) = e then
								Add(quotients, [ab,ac,ad,bc,bd,cd]);
							fi;
						od;
					od;
				od;
			od;
		od;
	od;
	return quotients;
end;

run := function(n)
	local quotients, q, f, rels, a,b,c,d;
	f := free4();
	a := GeneratorsOfMonoid(f)[1];
	b := GeneratorsOfMonoid(f)[2];
	c := GeneratorsOfMonoid(f)[3];
	d := GeneratorsOfMonoid(f)[4];
	for q in [5 .. n] do
		rels := torusRels(4,q,f, [a,a*b*a,a*b*c*b*a,a*b*c*d*c*b*a]);
		Print("T(4,",q,"): ", coxQuotient(f, rels), "\n");
	od;
end;

checkConjecture := function(n)
	local quotients, q, f, rels, a,b,c,d,e;
	f := free4();
	rws := coxeterRws(3,2,2,3,2,3,f);
	a := GeneratorsOfMonoid(f)[1];
	b := GeneratorsOfMonoid(f)[2];
	c := GeneratorsOfMonoid(f)[3];
	d := GeneratorsOfMonoid(f)[4];
	e := UnderlyingElement(One(f));
	for q in [5,10 .. n] do
		rels := torusRels(4,q,f, [a,a*b*a,a*b*c*b*a,a*b*c*d*c*b*a]);
		Print("T(4,",q,"): ", ReducedForm(rws, rels[1]),ReducedForm(rws, rels[2]),ReducedForm(rws, rels[3]) , "\n");
	od;
end;
