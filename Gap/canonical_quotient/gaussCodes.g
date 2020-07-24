

DeclareProperty("IsGaussCode", IsHomogeneousList);

#TODO do right
InstallMethod(IsGaussCode,  [IsHomogeneousList],
function(list)
	return true;
end);

DeclareAttribute("NumberOfComponents", IsGaussCode);
InstallMethod(NumberOfComponents, "for homogeneous lists", [IsHomogeneousList],
function(C) 
	return Length(C);
end);

DeclareProperty("IsKnot", IsGaussCode);
InstallMethod(IsKnot, "for Gauss codes", [IsGaussCode], 
C -> NumberOfComponents(C) = 1);

DeclareProperty("IsProperLink", IsGaussCode);
InstallMethod(IsProperLink, "for Gauss codes", [IsGaussCode],
C -> NumberOfComponents(C) > 1);

DeclareAttribute("Arcs", IsGaussCode);
InstallMethod(Arcs, "for Gauss codes", [IsGaussCode],
function(C)
	
end);