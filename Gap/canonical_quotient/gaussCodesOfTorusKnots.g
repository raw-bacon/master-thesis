#WRONG FUCK (but works for p = 3)
gaussCodeTorus := function(p,q)
	local code, list, k, lastEndOfCycle;
	if Gcd(p,q) <> 1 then return fail; fi;
	code := [];
	lastEndOfCycle := 2*(p-1);
	for k in [1 .. q] do
		Append(code, List([1 .. p-1], n -> (n + 2*(k-1)*p - 1) mod ((p-1)*q) + 1));
		Append(code, List([2*(p-1), 3*(p-1) - 1 .. p*(p-1) - p + 2], n -> -((n + 2*(k-1)*p - 1) mod ((p-1)*q) + 1)));
	od;
	
	return code;
end;