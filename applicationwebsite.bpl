// Each ApplicationWebsite has its own map of college
// I use mapOfColleges from mapcollege.bpl
//var mapOfAvailableColleges : [Ref]MapIntCollege;

var packedApplicationWebsiteField : [Ref]bool;
var fracApplicationWebsiteField : [Ref]real;

procedure PackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires (packedApplicationWebsiteField[this]==false) &&
 	(mapOfColleges[this] == m); 

procedure UnpackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires packedApplicationWebsiteField[this];
ensures	(mapOfColleges[this] == m); 

procedure submitApplicationGetCollege(int collegeNumber) returns (r: Ref)
// TODO add modifies
requires packedApplicationWebsiteField[this] && 
	(fracApplicationWebsiteField[this] > 0.0);

ensures ( packedCollegeBuildingsFew[result] && 
	(fracCollegeBuildingsFew[result] > 0.0) ) ||
	( packedCollegeBuildingsMany[result] &&
	(fracCollegeBuildingsMany[result] > 0.0) );
{
	var college : Ref;
	call college := lookup(collegeNumber, mapOfColleges[this]);
	// might be able to say var r : Ref from the beginning
	r := college;
}

procedure main(this:Ref) 
// TODO add modifies
{
	var website : Ref;
	var college, college2 : Ref;
	var app1, app2 : Ref;
	var app3, app4 : Ref;
	assume (college != college2);
	assume (app1 != app2);
	assume (app3 != app4);
	
	call ConstructApplicationWebsite(5, website);
	packedApplicationWebsiteField[website] := false;
	call PackApplicationWebsiteField(mapOfColleges[website], website);
	packedApplicationWebsiteField[website] := true;
	fracApplicationWebsiteField[website] := 1.0;

	call college := submitApplicationGetCollege(2, website);

	call ConstructStudentApplication(college, 3, app1);
	packedStudentAppFacilitiesFew[app1] := false;
	call PackStudentAppFacilitiesFew(college, 3, app1);
	packedStudentAppFacilitiesFew[app1] := true;
	fracStudentAppFacilitiesFew[app1] := 1.0;
	fracCollegeFacilitiesFew[college] := fracCollegeFacilitiesFew[college] / 2.0;

	call ConstructStudentApplication(college, 2, app2);
	packedStudentAppFacilitiesFew[app2] := false;
	call PackStudentAppFacilitiesFew(college, 2, app2);
	packedStudentAppFacilitiesFew[app2] := true;
	fracStudentAppFacilitiesFew[app2] := 1.0;
	fracCollegeFacilitiesFew[college] := fracCollegeFacilitiesFew[college] / 2.0;

	call checkFewFacilities(app1);
	call changeApplicationFew(34, app1);
	call checkFewFacilities(app2);

	// ---- code below this is similar to above

	call college2 := submitApplicationGetCollege(56, website);

	call ConstructStudentApplication(college2, 45, app3);
	packedStudentAppFacilitiesMany[app3] := false;
	call PackStudentAppFacilitiesMany(college2, 45, app3);
	packedStudentAppFacilitiesMany[app3] := true;
	fracStudentAppFacilitiesMany[app3] := 1.0;
	fracCollegeFacilitiesMany[college] := fracCollegeFacilitiesMany[college2] / 2.0;

	call ConstructStudentApplication(college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := false;
	call PackStudentAppFacilitiesMany(college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := true;
	fracStudentAppFacilitiesMany[app4] := 1.0;
	fracCollegeFacilitiesMany[college2] := fracCollegeFacilitiesMany[college2] / 2.0;

	call checkFewFacilities(app3);
	call changeApplicationFew(78, app3);
	call checkFewFacilities(app4);
}


