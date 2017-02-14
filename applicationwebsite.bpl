type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.

var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;

// Each ApplicationWebsite has its own map of college

var packedApplicationWebsiteField : [Ref]bool;
var fracApplicationWebsiteField : [Ref]real;

procedure PackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires (packedApplicationWebsiteField[this]==false);
requires (mapOfColleges[this] == m); 
// TODO add something about params, the values can be null or not
requires  (forall j:int :: (  ((j<=maxSize[this]) && (j>=0)) ==> 
           packedKeyValuePair[this, j] && (fracKeyValuePair[this, j] > 0.0) ) );

procedure UnpackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires packedApplicationWebsiteField[this];
requires fracApplicationWebsiteField[this] > 0.0;
ensures	(mapOfColleges[this] == m);
// TODO add something about params, the values can be null or not
ensures  (forall j:int :: (  ((j<=maxSize[this]) && (j>=0)) ==> 
           packedKeyValuePair[this, j] && (fracKeyValuePair[this, j] > 0.0) ) );

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index, the key, 
// that we need in order to get to the value.
var packedKeyValuePair : [Ref, int]bool;
var fracKeyValuePair : [Ref, int]real;

procedure PackKeyValuePair(m:MapIntCollege, key:int, value:Ref, this:Ref);
requires packedKeyValuePair[this, key] == false;
requires mapOfColleges[this] == m;
requires  (m[key] == value);

procedure UnpackKeyValuePair(m:MapIntCollege, key:int, value:Ref, this:Ref);
requires packedKeyValuePair[this, key];
requires fracKeyValuePair[this, key] > 0.0;
ensures (mapOfColleges[this] == m);
ensures (m[key] == value);

procedure createMapCollege(maxSize1:int, this: Ref)
modifies maxSize, mapOfColleges, packedKeyValuePair, fracKeyValuePair;
requires (maxSize1>=0);
// TODO add something about param being null in the ensures below
ensures (forall j:int :: ((j<=maxSize1) && (j>=0)) ==> (packedKeyValuePair[this, j] && (fracKeyValuePair[this, j]==1.0)) ) ;
ensures maxSize[this] == maxSize1;
{
call makeMapNull(maxSize1, this);
maxSize[this] := maxSize1;
}

procedure makeMapNull(i : int, this:Ref)
modifies mapOfColleges, packedKeyValuePair, fracKeyValuePair;
requires (i>=0);
ensures (forall j:int :: (((j<=i) && (j>=0) ) ==> (packedKeyValuePair[this, j] && ( fracKeyValuePair[this, j] == 1.0 )))  );
{
if (i==0) {
	mapOfColleges[this][i] := null;	
  	packedKeyValuePair[this, i] := true;
  	fracKeyValuePair[this, i] := 1.0;
} else if (i>0) {
	call makeMapNull(i-1, this);
  	mapOfColleges[this][i] := null;	
  	packedKeyValuePair[this, i] := true;
  	fracKeyValuePair[this, i] := 1.0;
}
}

procedure containsKey(key1: int, this:Ref) returns (b:bool);
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
//requires this#k MapOfCollegesField()
ensures (b == true) ==> packedKeyValuePair[this, key1] && (fracKeyValuePair[this, key1] > 0.0);
ensures (b == false) ==> packedKeyValuePair[this, key1] && (fracKeyValuePair[this, key1] > 0.0) &&(mapOfColleges[this][key1]== null);
//{
//	b := true;
//	if (mapOfColleges[this][key1] == null) {
//		b := false;	
//	} 
//}
	
procedure put(key1 : int, college1: Ref, this:Ref) ;
modifies mapOfColleges, packedKeyValuePair;
requires packedApplicationWebsiteField[this]==false;
requires (fracApplicationWebsiteField[this] > 0.0);
// This put procedure will be called with null for the value in packedKeyValuePair.
requires packedKeyValuePair[this, key1];
requires (fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
//{
//  call UnpackKeyValuePair(mapOfColleges[this], key1, null, this);
//  packedKeyValuePair[this, key1] := false;
//	mapOfColleges[this][key1] := college1;	
//  call PackKeyValuePair(mapOfColleges[this], key1, college1, this);
//  packedKeyValuePair[this, key1] := true;
// }
	
procedure get(key1:int, this:Ref) returns (c:Ref);
requires packedKeyValuePair[this, key1];
requires	(fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
ensures packedCollegeNumberField[c];
ensures fracCollegeNumberField[c] > 0.0;
//requires this#k MapOfCollegesField()
//ensures this#k KeyValuePair(key1, result)
//{
//	c := mapOfColleges[this][key1];
//}
	
procedure lookup(collegeNumber:int, this:Ref) returns (r:Ref)
modifies mapOfColleges, packedCollegeNumberField, fracCollegeNumberField,collegeNumber,
       endowment, packedKeyValuePair, packedApplicationWebsiteField;
requires (collegeNumber<=maxSize[this]) && (0<=collegeNumber);
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
ensures packedKeyValuePair[this, collegeNumber];
ensures	(fracKeyValuePair[this, collegeNumber] > 0.0);
ensures packedCollegeNumberField[r];
ensures fracCollegeNumberField[r] > 0.0;

//ensures this#k KeyValuePair(collegeNumber, result)
{
var temp:bool;
var c:Ref;
call temp := containsKey(collegeNumber, this);
call UnpackApplicationWebsiteField(mapOfColleges[this], this);
packedApplicationWebsiteField[this]:=false;
if (temp == false) 
	{
		call ConstructCollege(collegeNumber, c);
		packedCollegeNumberField[c] := false;
		call PackCollegeNumberField(collegeNumber, c);
		packedCollegeNumberField[c] := true;
		fracCollegeNumberField[c] := 1.0;
    
		call put(collegeNumber, c, this);
	}
call r:= get(collegeNumber, this);
}

procedure ConstructApplicationWebsite(maxSize1:int, this:Ref)
modifies maxSize, mapOfColleges, packedKeyValuePair, fracKeyValuePair;
requires (maxSize1>=0);
ensures (forall j:int :: ((j<=maxSize1) && (j>=0)) ==> (packedKeyValuePair[this, j] && (fracKeyValuePair[this, j]==1.0)) ) ;
ensures maxSize[this] == maxSize1;
{
	call createMapCollege(maxSize1, this);
 }

procedure submitApplicationGetCollege(collegeNumber:int, this:Ref) returns (r: Ref)
modifies mapOfColleges, packedCollegeNumberField, fracCollegeNumberField, collegeNumber, endowment,
        packedKeyValuePair, packedApplicationWebsiteField;
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
requires (collegeNumber<=maxSize[this]) && (0<=collegeNumber);
ensures packedCollegeNumberField[r];
ensures fracCollegeNumberField[r] > 0.0;
{
	call r := lookup(collegeNumber, this);
  
}

procedure main1(this:Ref) 
modifies mapOfColleges, packedApplicationWebsiteField,
  packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany,
  packedCollegeNumberField, fracCollegeNumberField, collegeNumber, endowment,
  fracApplicationWebsiteField, college, facilities, campusNumber, 
  fracMultipleOf, packedMultipleOf, fracStudentAppFacilitiesFew,
  fracStudentAppFacilitiesMany, maxSize, divider, value,
  fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
  packedKeyValuePair, fracKeyValuePair,
        packedCollegeFacilitiesFew, packedCollegeFacilitiesMany, packedCollegeNumberField,
        fracCollegeNumberField;
{
	var website : Ref;
	var college : Ref;
	var app1, app2: Ref;
  	var tempbo : bool;
	assume (app1 != app2);
	
	call ConstructApplicationWebsite(100, website);
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

 //transfer
  packedCollegeNumberField[college] := packedCollegeFacilitiesFew[college];
  fracCollegeNumberField[college] := fracCollegeFacilitiesFew[college];
  
	call ConstructStudentApplication(college, 2, app2);
	packedStudentAppFacilitiesFew[app2] := false;
	call PackStudentAppFacilitiesFew(college, 2, app2);
	packedStudentAppFacilitiesFew[app2] := true;
	fracStudentAppFacilitiesFew[app2] := 1.0;
	fracCollegeFacilitiesFew[college] := fracCollegeFacilitiesFew[college] / 2.0;

	call tempbo := checkFacilitiesFew(app1);
	call changeApplicationFew(34, app1);
	call tempbo := checkFacilitiesFew(app2);
}

// ---- procedure below is similar to above

procedure main2(this:Ref) 
modifies mapOfColleges, packedApplicationWebsiteField,
  packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany,
  packedCollegeNumberField, fracCollegeNumberField, collegeNumber, endowment,
  fracApplicationWebsiteField, college, facilities, campusNumber, 
  fracMultipleOf, packedMultipleOf, fracStudentAppFacilitiesFew,
  fracStudentAppFacilitiesMany, maxSize, divider, value,
  fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
  packedKeyValuePair, fracKeyValuePair,
        packedCollegeFacilitiesFew, packedCollegeFacilitiesMany,
        packedCollegeNumberField, fracCollegeNumberField;
{
	var website : Ref;
	var college2 : Ref;
	var app3, app4 : Ref;
  	var tempbo : bool;
	assume (app3 != app4);
  
  	call ConstructApplicationWebsite(100, website);
	packedApplicationWebsiteField[website] := false;
	call PackApplicationWebsiteField(mapOfColleges[website], website);
	packedApplicationWebsiteField[website] := true;
	fracApplicationWebsiteField[website] := 1.0;
  
	call college2 := submitApplicationGetCollege(56, website);

	call ConstructStudentApplication(college2, 45, app3);
	packedStudentAppFacilitiesMany[app3] := false;
	call PackStudentAppFacilitiesMany(college2, 45, app3);
	packedStudentAppFacilitiesMany[app3] := true;
	fracStudentAppFacilitiesMany[app3] := 1.0;
	fracCollegeFacilitiesMany[college2] := fracCollegeFacilitiesMany[college2] / 2.0;
  
   //transfer
  packedCollegeNumberField[college2] := packedCollegeFacilitiesMany[college2];
  fracCollegeNumberField[college2] := fracCollegeFacilitiesMany[college2];

	call ConstructStudentApplication(college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := false;
	call PackStudentAppFacilitiesMany(college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := true;
	fracStudentAppFacilitiesMany[app4] := 1.0;
	fracCollegeFacilitiesMany[college2] := fracCollegeFacilitiesMany[college2] / 2.0;

	call tempbo := checkFacilitiesMany(app3);
	call changeApplicationMany(78, app3);
  
	call tempbo := checkFacilitiesMany(app4);
}
