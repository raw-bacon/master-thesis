

gaussCodeFromBraid := function(braid)
	
	crossings := [1 .. Length(braid)];
	position := 1;
	gaussCode := List([1 .. numberOfComponents], x -> []);
	next := 1;
	component := 0;
	for i in [1 .. Length(braid)] do
		if next = 1 then
			component := component + 1;
		else
			Add(gaussCode[component], next);
		fi;
		
		
	od;
	return gaussCode;
end;