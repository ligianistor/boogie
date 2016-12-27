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
	
	call ConstructApplicationWebsite(website);
	// TODO add the right statements after this constructor
	// ApplicationWebsite website = new ApplicationWebsite()();

	call college := submitApplicationGetCollege(2, website);

	call ConstructStudentApplication(college, 3, app1);
	//TODO write the needed statements after this constructor
	// StudentApplication app1 = new StudentApplication(StudentAppFacilitiesFew())(college, 3);

	call ConstructStudentApplication(college, 2, app2);
	// TODO write after constructor
	// StudentApplication app2 = new StudentApplication(StudentAppFacilitiesFew())(college, 2);

	call checkFewFacilities(app1);
	call changeApplicationFew(34, app1);
	call checkFewFacilities(app2);

	// ---- code below this is similar to above

	call college2 := submitApplicationGetCollege(56, website);

	call ConstructStudentApplication(college2, 45, app3);
	//TODO write the needed statements after this constructor
	// StudentApplication app3 = new StudentApplication(StudentAppFacilitiesMany())(college2, 45);

	call ConstructStudentApplication(college2, 97, app4);
	// TODO write after constructor
	// StudentApplication app4 = new StudentApplication(StudentAppFacilitiesMany())(college2, 97);

	call checkFewFacilities(app3);
	call changeApplicationFew(78, app3);
	call checkFewFacilities(app4);
}






