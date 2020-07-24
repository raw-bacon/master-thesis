determinant := function(code)
	local setArcs, n, matrix, count, i, j, k, c;
	setArcs := arcs(code);
	n := Length(setArcs);
	matrix := List([1 .. n], k -> List([1 .. n], j -> 0));
	count := 1;
	for c in crossings(code) do
		i := Position(setArcs, c[1]);
		j := Position(setArcs, c[2]);
		k := Position(setArcs, c[3]);
		matrix[count][i] := 2;
		matrix[count][j] := -1;
		matrix[count][k] := -1;
		count := count + 1;
	od;
	matrix := matrix{[1 .. n - 1]}{[1 .. n - 1]};
	return AbsInt(Determinant(matrix));
end;