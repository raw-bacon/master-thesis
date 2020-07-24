densify := function(list)
	local denseList, element;
	denseList := [];
	for element in list do
		Add(denseList, element);
	od;
	return denseList;
end;

#sees that the variables are of the form -n .. -1, 1 .. n
rename := function(list)
	local maximalNode, name, max;
	list := ShallowCopy(list);
	maximalNode := Int(Length(list) / 2);
	for name in [1 .. maximalNode] do
		if not name in list then
			max := Maximum(list);
			list[Position(list, max)] := name;
			list[Position(list, -max)] := -name;
		fi;
	od;
	return list;
end;


star := function(code)
	local i, index1, index2, indices;
	code := ShallowCopy(code);
	for i in [1 .. Maximum(code)] do
		indices := [Position(code, i), Position(code, -i)];
		index1 := Minimum(indices);
		index2 := Maximum(indices);
		code{[index1 + 1 .. index2 - 1]} := Reversed(code{[index1 + 1 .. index2 - 1]});
	od;
	return code;
end;


#does not work but returns fail if <code> is not planar
orientationsOfCode := function(code)
	local codeStar, up, orientations, overEnds, underEnds, i, j, data, possibleMistakes, backup, copy;
	codeStar := star(code);
	orientations := [];
	overEnds := [];
	underEnds := [];
	possibleMistakes := [];
	backup := [];
	i := 1;
	while i <= Length(code) do
		j := Position(codeStar, -codeStar[i]);
		if i in overEnds then
			orientations[i] := orientations[j];
			Remove(overEnds, Position(overEnds, i));
		elif i in underEnds then
			orientations[i] := orientations[j];
			Remove(underEnds, Position(underEnds, i));
		elif (overEnds = [] or j < Minimum(overEnds)) and not i in possibleMistakes then
			Add(overEnds, j);
			#actually you would need to trace the knot to see whether the directions are the same or opposite
			if codeStar[i] < 0 then
				orientations[i] := -1;
			else
				orientations[i] := 1;
			fi;
			if (underEnds = [] or j < Minimum(underEnds)) and i <> 1 then
				Add(possibleMistakes,i);
				Add(backup, [ShallowCopy(orientations), 
							 ShallowCopy(overEnds), 
							 ShallowCopy(underEnds), 
							 ShallowCopy(possibleMistakes), i-1]);
			fi;
		elif underEnds = [] or j < Minimum(underEnds) then
			Add(underEnds, j);
			if codeStar[i] < 0 then
				orientations[i] := 1;
			else
				orientations[i] := -1;
			fi;
		else
			if backup <> [] then
				data := Remove(backup);
				orientations := data[1];
				overEnds := data[2];
				underEnds := data[3];
				possibleMistakes := data[4];
				i := data[5];
				Remove(overEnds);
			else
				return fail;
			fi;
		fi;
		i := i + 1;
	od;
	
	#permuting orientations back to original positions
	copy := ShallowCopy(orientations);
	for i in [1 .. Length(code)] do
		orientations[i] := copy[Position(codeStar, code[i])];
	od;
	return orientations;
end;

evenlyIntersticed := function(code)
	local index, visited;
	visited := [];
	for index in [1 .. Length(code)] do
		if not index in visited then
			if Size(code{[index .. Position(code, -code[index])]}) mod 2 = 1 then
				return false;
			fi;
		fi;
	od;
	return true;
end;


valid := code -> evenlyIntersticed(code) and orientationsOfCode(code) <> fail;


#returns the index of the next crossing to the left
nextLeft := function(code, index)
	local orientations, indexOfNegative, under;
	orientations := orientationsOfCode(code);
	indexOfNegative := Position(code, -code[index]);
	if code[index] < 0 then
		under := -1;
	else
		under := 1;
	fi;
	if indexOfNegative + under*orientations[index] = 0 then
		return Length(code);
	elif indexOfNegative + under*orientations[index] = Length(code) + 1 then
		return 1;
	else
		return indexOfNegative + under*orientations[index];
	fi;
end;


#adds a crossing at index. assumes that the gauss code makes sense.
reidemeisterOneAddCrossing := function(code, orientation, index)
	local newNumber;
	code := ShallowCopy(code);
	if code <> [] then
		newNumber := Maximum(code) + 1;
	else
		newNumber := 1;
	fi;
	Add(code, orientation * newNumber, index);
	Add(code, - orientation * newNumber, index);
	return code;
end;


#removes all reidemeister type one crossings if there are any.
#otherwise does nothing
reidemeisterOneRemoveAllCrossings := function(code)
	local i;
	code := rename(densify(code));
	for i in [1 .. Length(code) - 1] do
		if code[i] = - code[i + 1] then
			Unbind(code[i]);
			Unbind(code[i+1]);
			return rename(densify(reidemeisterOneRemoveAllCrossings(code)));
		fi;
	od;
	if code[1] = - code[Length(code)] then
		Unbind(code[1]);
		Unbind(code[Length(code)]);
		return rename(densify(reidemeisterOneRemoveAllCrossings(code)));
	fi;
	return rename(densify(code));
end;

reidemeisterOneRemoveCrossing := function(code, index)
	code := ShallowCopy(code);
	if index in [1 .. Length(code) - 1] then
		Unbind(code[index]);
		Unbind(code[index+1]);
	elif index = Length(code) then
		Unbind(code[1]);
		Unbind(code[Length(code)]);
	else
		return fail;
	fi;
	return rename(densify(code));
end;

reidemeisterOneRemovePossibilities := function(code)
	local i, list;
	list := [];
	for i in [1 .. Length(code) - 1] do
		if code[i] = - code[i + 1] then
			Add(list, i);
		fi;
	od;
	if code <> [] and code[1] = - code[Length(code)] then
		Add(list, Length(code));
	fi;
	return list;
end;

#removes all reidemeister type two crossings if there are any.
#otherwise does nothing
reidemeisterTwoRemoveAllCrossings := function(code)
	local index, node1, node2;
	code := ShallowCopy(code);
	index := 1;
	while index <= Length(code) - 3 do
		node1 := code[index];
		node2 := code[index + 1];
		
		if node1 = - node2 then
			#nothing
		
		elif Position(code, -node1) < Length(code) and code[Position(code, -node1) + 1] = -node2 then
			Unbind(code[index]);
			Unbind(code[index+1]);
			Unbind(code[Position(code,-node1)]);
			Unbind(code[Position(code,-node2)]);
			code := rename(densify(code));
			index := 0;
		
		elif Position(code, -node2) < Length(code) and code[Position(code, -node2) + 1] = -node1 then
			Unbind(code[index]);
			Unbind(code[index+1]);
			Unbind(code[Position(code, -node2)]);
			Unbind(code[Position(code, -node1)]);
			code := rename(densify(code));
			index := 0;
		
		elif Position(code, -node1) = Length(code) and code[1] = -node2 then
			Unbind(code[index]);
			Unbind(code[index+1]);
			Unbind(code[Position(code, -node2)]);
			Unbind(code[Position(code, -node1)]);
			code := rename(densify(code));
			index := 0;
			
		elif Position(code, -node2) = Length(code) and code[1] = -node1 then
			Unbind(code[index]);
			Unbind(code[index+1]);
			Unbind(code[Position(code, -node2)]);
			Unbind(code[Position(code, -node1)]);
			code := rename(densify(code));
			index := 0;
			
		fi;
		index := index + 1;
	od;
	return rename(densify(code));	
end;


reidemeisterTwoRemoveCrossing := function(code, index)
	local node1, node2;
	code := ShallowCopy(code);
	node1 := code[index];
	node2 := code[index + 1];
	if (Position(code,-node1) = Length(code) and code[1] = -node2) or
	   (Position(code,-node2) = Length(code) and code[1] = -node1) or
	   (Position(code,-node1) < Length(code) and code[Position(code,-node1)+1] = -node2) or
	   (Position(code,-node2) < Length(code) and code[Position(code,-node2)+1] = -node1) then
		Unbind(code[index]);
		Unbind(code[index+1]);
		Unbind(code[Position(code, -node2)]);
		Unbind(code[Position(code, -node1)]);
		code := rename(densify(code));
	else
		return fail;
	fi;
	return code;
end;

reidemeisterTwoRemovePossibilities := function(code)
	local list, index, node1, node2;
	list := [];
	for index in [1 .. Length(code) - 3] do
		node1 := code[index];
		node2 := code[index + 1];
		if node1 = -node2 or node1 * node2 < 0 then
			#nothing
		elif Position(code, -node1) < Length(code) and code[Position(code, -node1) + 1] = -node2 then
			Add(list, index);
		elif Position(code, -node2) < Length(code) and code[Position(code, -node2) + 1] = -node1 then
			Add(list, index);
		elif Position(code, -node1) = Length(code) and code[1] = -node2 then
			Add(list, index);
		elif Position(code, -node2) = Length(code) and code[1] = -node1 then
			Add(list, index);
		fi;
	od;
	return list;
end;


#returns fail if <upperIndex> = <lowerIndex>. otherwise introduces a reidemeister
#two type crossing
reidemeisterTwoAddCrossings := function(code, upperIndex, lowerIndex, orientation)
	local maximalNode;
	code := ShallowCopy(code);
	if code <> [] then
		maximalNode := Maximum(code);
	else
		maximalNode := 0;
	fi;
	Add(code, maximalNode + 1, upperIndex);
	Add(code, maximalNode + 2, upperIndex + 1);
	if orientation = 1 then
		if upperIndex < lowerIndex then
			Add(code, - maximalNode - 1, lowerIndex + 2);
			Add(code, - maximalNode - 2, lowerIndex + 3);
		else
			Add(code, - maximalNode - 1, lowerIndex);
			Add(code, - maximalNode - 2, lowerIndex + 1);
		fi;
	else
		if upperIndex < lowerIndex then
			Add(code, - maximalNode - 2, lowerIndex + 2);
			Add(code, - maximalNode - 1, lowerIndex + 3);
		else
			Add(code, - maximalNode - 2, lowerIndex);
			Add(code, - maximalNode - 1, lowerIndex + 1);
		fi;
	fi;
	return code;
end;

#experimental. not sure if correct
reidemeisterTwoAddCrossingsPossibilities := function(code)
	local poss, i, j, try;
	poss := [];
	for i in [1 .. Length(code) + 1] do
		for j in [1 .. Length(code) + 1] do
			try := reidemeisterTwoAddCrossings(code, i, j, 1);
			if valid(try) then
				Add(poss, [i,j,1]);
			fi;
			
			try := reidemeisterTwoAddCrossings(code, i, j, -1);
			if valid(try) then
				Add(poss, [i,j,-1]);
			fi;
		od;
	od;
	return poss;
end;


#functions to check for unnecessary crossings
hasReidemeisterOneCrossings := code -> not code = reidemeisterOneRemoveAllCrossings(code);
hasReidemeisterTwoCrossings := code -> not code = reidemeisterTwoRemoveAllCrossings(code);


#moves the strand between the crossings of index <indexArc1> and <indexArc2> over the 
#crossing with index <indexCrossing> in the gauss code.
#assume that <indexArc1> = <indexCrossing> +- 1 and that the reidemeister move
#makes sense, i.e. <indexArc2> = code[Position(-code[indexCrossing])] +- 1.
#to cover every possible reidemeister three move one can also assume that indexArc1 < indexArc2
reidemeisterThree := function(code, indexCrossing, indexArc1, indexArc2)
	local nameCrossing, nameArc1, nameArc2, indexMinusArc1, indexMinusArc2, indexMinusCrossing;
	#four cases. either indexArc1 is before indexCrossing or after.
	#same with indexArc2.
	
	if not (indexCrossing in [1 .. Length(code)] and
			indexArc1 in [1 .. Length(code)] and
			indexArc2 in [1 .. Length(code)]) then 
		return fail; 
	fi;
	
	code := ShallowCopy(code);
	
	nameCrossing := code[indexCrossing];
	nameArc1 := code[indexArc1];
	nameArc2 := code[indexArc2];
	
	indexMinusCrossing := Position(code, -nameCrossing);
	indexMinusArc1 := Position(code, -nameArc1);
	indexMinusArc2 := Position(code, -nameArc2);
	
	if not ((indexArc1 = indexCrossing + 1 or indexArc1 = indexCrossing - 1 or (indexArc1 = Length(code) and indexCrossing = 1)
			 or (indexArc1 = 1 and indexCrossing = Length(code)))
        and ((indexArc2 = indexMinusCrossing + 1 or indexArc2 = indexMinusCrossing - 1) or (indexArc2 = Length(code) and indexMinusCrossing = 1)
			 or (indexArc2 = 1 and indexMinusCrossing = Length(code)))
		and ((nameArc1 > 0 and nameArc2 > 0) or (nameArc1 < 0 and nameArc2 < 0))
		and indexCrossing <> indexArc1 and indexCrossing <> indexArc2 and indexMinusCrossing <> indexArc1 and indexMinusCrossing <> indexArc2
		and indexArc1 <> indexMinusArc2
		and (indexMinusArc1 = indexMinusArc2 + 1 or indexMinusArc1 = indexMinusArc2 - 1
			 or (indexMinusArc1 = 1 and indexMinusArc2 = Length(code)) or (indexMinusArc1 = Length(code) and indexMinusArc2 = 1))) then
		return fail;
	fi;
	
	code[indexCrossing] := nameArc1;
	code[indexArc1] := nameCrossing;
	code[indexMinusCrossing] := nameArc2;
	code[indexArc2] := -nameCrossing;
	code[indexMinusArc1] := -nameArc2;
	code[indexMinusArc2] := -nameArc1;
	return code;
end;

reidemeisterThreePossibilities := function(code)
	local list, indexCrossing, indexArc1, indexArc2;
	list := [];
	for indexCrossing in [1 .. Length(code)] do
		for indexArc1 in [1 .. Length(code)] do
			for indexArc2 in [indexArc1 + 1 .. Length(code)] do
				if reidemeisterThree(code, indexCrossing, indexArc1, indexArc2) <> fail then
					Add(list, [indexCrossing, indexArc1, indexArc2]);
				fi;
			od;
		od;
	od;
	return list;
end;


#a duplicate is a composition of renaming and cycling applied to a gauss code
removeDuplicates := function(listOfGaussCodes)
	local code, j, i;
	listOfGaussCodes := StructuralCopy(listOfGaussCodes);
	i := 1;
	while i <= Length(listOfGaussCodes) do
		for code in cycles(listOfGaussCodes[i]) do
			for j in [i + 1 .. Length(listOfGaussCodes)] do
				if isRenaming(code, listOfGaussCodes[j]) then
					Unbind(listOfGaussCodes[j]);
				fi;
			od;
			listOfGaussCodes := densify(listOfGaussCodes);
		od;
		if Length(listOfGaussCodes) > 10 then
			Print(i, " / ", Length(listOfGaussCodes), "\n");
		fi;
		i := i + 1;
	od;
	return densify(listOfGaussCodes);
end;


doAllPossibleMoves := function(code)
	local list, poss;
	list := [];
	#reidemeister 1 add crossings
	for poss in [1 .. Length(code) + 1] do
		Add(list, reidemeisterOneAddCrossing(code, 1, poss));
		Add(list, reidemeisterOneAddCrossing(code, -1, poss));
	od;
	
	#reidemeister 1 remove crossings
	for poss in reidemeisterOneRemovePossibilities(code) do
		Add(list, reidemeisterOneRemoveCrossing(code, poss));
	od;
	
	#reidemeister 2 add crossing
	for poss in reidemeisterTwoAddCrossingsPossibilities(code) do
		Add(list, reidemeisterTwoAddCrossings(code, poss[1], poss[2], poss[3]));
	od;
	
	#reidemeister 2 remove crossings
	for poss in reidemeisterTwoRemovePossibilities(code) do
		Add(list, reidemeisterTwoRemoveCrossing(code, poss));
	od;
	
	#reidemeister 3
	for poss in reidemeisterThreePossibilities(code) do
		Add(list, reidemeisterThree(code, poss[1], poss[2], poss[3]));
	od;
	
	return Set(removeDuplicates(list));
end;

doAllPossibleReidemeisterTwoMoves := function(code)
	local list, poss, i;
	list := [];
	
	for poss in reidemeisterTwoAddCrossingsPossibilities(code) do
		Add(list, reidemeisterTwoAddCrossings(code, poss[1], poss[2], poss[3]));
	od;
	
	for i in [1 .. Length(list)] do
		if reidemeisterOneRemovePossibilities(list[i]) <> [] then
			Unbind(list[i]);
		fi;
	od;
	return Set(removeDuplicates(densify(list)));
end;

doAllPossibleReidemeisterTwoMovesIterate := function(code, max)
	local list, i, j;  
	list := [code];
	for i in [1 .. max] do
		for j in [1 .. Length(list)] do
			Append(list, doAllPossibleReidemeisterTwoMoves(list[i]));
			#list := Set(removeDuplicates(list));
		od;
		list := Set(removeDuplicates(list));
	od;
	return list;
end;

cycles := function(code)
	local list, i;
	list := [code];
	for i in [2 .. Length(code)] do
		Add(list, Concatenation(code{[i .. Length(code)]}, code{[1 .. i - 1]}));
	od;
	return list;
end;

isRenaming := function(code1, code2)
	local index, node;
	if Length(code1) <> Length(code2) then return false; fi;
	
	for index in [1 .. Length(code1)] do
		if Position(code1, -code1[index]) <> Position(code2, -code2[index]) then
			return false;
		fi;
	od;
	return true;
end;



allCodes := function(code, maxDistance)
	local i, list, c, newList;
	list := [code];
	for i in [1 .. maxDistance] do
		newList := ShallowCopy(list);
		for c in list do
			Append(newList, doAllPossibleMoves(c));
		od;
		
		list := Set(removeDuplicates(newList));
	od;
	return list;
end;



connectedSum := function(code1, code2)
	local max1, i;
	max1 := Maximum(code1);
	code2 := ShallowCopy(code2);
	for i in [1 .. Length(code2)] do
		if code2[i] > 0 then
			code2[i] := code2[i] + max1;
		else
			code2[i] := code2[i] - max1;
		fi;
	od;
	return Concatenation(code1,code2);
end;