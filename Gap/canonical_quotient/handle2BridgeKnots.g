#handles 2-bridge knots

#depends on canonicalQuotientFromGaussCode.g
Read("../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/canonicalQuotientFromGaussCode.g");

handleList := function(list)
	local code, g, out, path;
	path := "../../Users/levir/OneDrive/Desktop/studium/Documents/Masterarbeit/Gap/canonical_quotient/tables/2bridge.csv";
	
	
	out := [];
	for code in list do
		g := (canonicalQuotient(code));
		Add(out, Order(g) / 2);
		Print(Position(list, code), ".: ",  Order(g) / 2, "\n");
	od;
	
	#nicer would be to write it into csv
	#PrintCSV(path, out);
	return out;
end;