type Ref;
const null: Ref;

var value: [Ref]int;
var divider : [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedBasicIntCell: [Ref] bool;
var fracBasicIntCell: [Ref] real;

function modulo(x:int, y:int) returns (int);
axiom (forall x:int, y:int :: {modulo(x,y)} 
    ((0 <= x) &&(0 < y) ==> (0 <= modulo(x,y) ) && (modulo(x,y) < y) )
    &&
    ((0 <= x) &&(y < 0) ==> (0 <= modulo(x,y) ) && (modulo(x,y) < -y) )
    &&
    ((x <= 0) &&(0 < y) ==> (-y <= modulo(x,y) ) && (modulo(x,y) <= 0) )
    &&
    ((x <= 0) &&(y < 0) ==> (y <= modulo(x,y) ) && (modulo(x,y) <= 0) )
   ); 

// TODO need to be able to go from BasicIntCell to one of
// the more complex predicates and back.
procedure PackBasicIntCell(a: int, v:int, this:Ref);
requires (packedBasicIntCell[this]==false);
requires (value[this] == v);
requires (divider[this] == a);

procedure UnpackBasicIntCell(a: int, v:int, this:Ref);
requires packedBasicIntCell[this];
requires fracBasicIntCell[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);

procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false);
requires (value[this] == v);
requires (divider[this] == a);
requires (modulo(v,a) == 0); 

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);
ensures	(modulo(v,a) == 0); 

procedure ConstructIntCell(x: int, this: Ref);
ensures (value[this] == x);

procedure setValueMultiple3(x: int, divi:int, this: Ref) 
modifies value, divider,
      packedMultipleOf, fracMultipleOf;
//requires (fracBasicIntCell[this] == 1.0); 
requires (fracMultipleOf[this] > 0.0);
requires packedMultipleOf[this];
//requires (divider[this] == 21) || 
//	(divider[this] == 15) ||
//	(divider[this] == 33) ;
ensures (divider[this] == divi);
ensures (fracMultipleOf[this] > 0.0);
ensures packedMultipleOf[this];
{
	value[this] := x;
  divider[this] := divi;
}

procedure setValueMultiple2(x: int, divi:int, this: Ref) 
modifies value, divider,
      packedMultipleOf, fracMultipleOf;
//requires (fracBasicIntCell[this] == 1.0); 
requires (fracMultipleOf[this] > 0.0);
requires packedMultipleOf[this];
//requires  (divider[this] == 16) ||
//	 (divider[this] == 14) ||
//	 (divider[this] == 4);
ensures (divider[this] == divi);
ensures (fracMultipleOf[this] > 0.0);
ensures packedMultipleOf[this];
{
	value[this] := x;
  divider[this] := divi;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r:=value[this];
}
//-------------------

var packedCollegeBuildingsFew : [Ref] bool;
var fracCollegeBuildingsFew : [Ref] real;
var packedCollegeBuildingsMany : [Ref] bool;
var fracCollegeBuildingsMany : [Ref] real;

var collegeNumber :[Ref]int;
var endowment : [Ref]int;

var packedCollegeNumberField : [Ref]bool;
var fracCollegeNumberField : [Ref]real;

var packedCollegeFacilitiesMany : [Ref]bool;
var fracCollegeFacilitiesMany : [Ref]real;

var packedCollegeFacilitiesFew : [Ref]bool;
var fracCollegeFacilitiesFew : [Ref]real;

var packedCollegeFields : [Ref]bool;
var fracCollegeFields : [Ref]real;

procedure PackCollegeNumberField(c: int, this:Ref);
requires (packedCollegeNumberField[this]==false);
requires (collegeNumber[this] == c); 

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
requires fracCollegeNumberField[this] > 0.0;
ensures	(collegeNumber[this] == c);

procedure PackCollegeFields(c: int, this:Ref);
requires (packedCollegeFields[this]==false);
requires (collegeNumber[this] == c);
requires (endowment[this] == c*1000 - 5); 

procedure UnpackCollegeFields(c:int, this:Ref);
requires packedCollegeFields[this];
requires fracCollegeFields[this] > 0.0;
ensures	(collegeNumber[this] == c);
ensures (endowment[this] == c*1000 - 5);

procedure PackCollegeFacilitiesMany(num:int, c:int, this:Ref);
requires (packedCollegeFacilitiesMany[this] == false);
//TODO all Pack procedures need to refer to frac also, 
// not only to packed.
requires (collegeNumber[this] == c) && (num >= 10 * c);

procedure UnpackCollegeFacilitiesMany(num:int, c:int, this:Ref);
requires packedCollegeFacilitiesMany[this];
requires fracCollegeFacilitiesMany[this] > 0.0;
//TODO all Unpack procedures need to refer to frac also, 
// not only to packed.
ensures (collegeNumber[this] == c);
ensures	(num >= 10 * c);

procedure PackCollegeFacilitiesFew(num:int, c:int, this:Ref);
requires (packedCollegeFacilitiesFew[this] == false);
requires (collegeNumber[this] == c);
requires (num <= 4 * c);

procedure UnpackCollegeFacilitiesFew(num:int, c:int, this:Ref);
requires packedCollegeFacilitiesFew[this];
requires fracCollegeFacilitiesFew[this] > 0.0;
ensures (collegeNumber[this] == c);
ensures	(num <= 4 * c);

procedure ConstructCollege(number:int, this:Ref) 
modifies collegeNumber, endowment;
ensures packedCollegeFields[this] &&
	(fracCollegeFields[this] > 0.0);
// TODO need to put in statements about the parameters.
// ensures this#k CollegeFields()[number, (number*1000)-5]
{
	collegeNumber[this] := number;
	endowment[this] := (number *1000) - 5;
}

procedure getCollegeNumber(this:Ref) returns (r:int)
ensures packedCollegeNumberField[this] &&
	(fracCollegeNumberField[this] > 0.0);
// TODO add statement about value of parameter 
// ensures this#k CollegeNumberField()[result]
{
	r := collegeNumber[this];
}

// the method that calculates the extrinsic state
procedure getNumberFacilities(campusNumber:int, this:Ref) returns (r:Ref)
requires packedCollegeNumberField[this];
requires (fracCollegeNumberField[this] > 0.0);
//TODO have to say what are the current values of the parameters
// requires this#1 CollegeNumberField(this.collegeNumber)
ensures packedMultipleOf[r] &&
	(fracMultipleOf[r] > 0.0);
//ensures result#1 MultipleOf(this.collegeNumber)
{
	call ConstructIntCell(collegeNumber[this] * campusNumber, r);
	packedMultipleOf[r] := false;
	call PackMultipleOf(collegeNumber[this], collegeNumber[this] * campusNumber, r);
	packedMultipleOf[r] := true;
	fracMultipleOf[r] := 1.0;
}

//---------------------------

type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.
// This field is common with ApplicationWebsite.

var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index, the key, 
// that we need in order to get to the value.
var packedIsEntryNull : [Ref, int]bool;
var fracIsEntryNull : [Ref, int]real;

//TODO maybe this one has to be like the one above
var packedKeyValuePair : [Ref]bool;
var fracKeyValuePair : [Ref]real;

var packedMapOfCollegesField : [Ref]bool;
var fracMapOfCollegesField : [Ref]real;

procedure PackMapOfCollegesField(m:MapIntCollege, this:Ref);
requires packedMapOfCollegesField[this] == false;
requires mapOfColleges[this] == m;

procedure UnpackMapOfCollegesField(m:MapIntCollege, this:Ref);
requires packedMapOfCollegesField[this];
requires fracMapOfCollegesField[this] > 0.0;
ensures mapOfColleges[this] == m;

procedure PackKeyValuePair(m:MapIntCollege, key:int, value:Ref, this:Ref);
requires packedKeyValuePair[this] == false;
requires mapOfColleges[this] == m;
requires  (m[key] == value);

procedure UnpackKeyValuePair(m:MapIntCollege, key:int, value:Ref, this:Ref);
requires packedKeyValuePair[this];
requires fracKeyValuePair[this] > 0.0;
ensures mapOfColleges[this] == m;
ensures (m[key] == value);

procedure PackIsEntryNull(key1 : int, m:MapIntCollege, this:Ref);
requires  (packedIsEntryNull[this] == false);
requires (mapOfColleges[this] == m);
requires (m[key1] == null);

procedure ConstructMapCollege(m: MapIntCollege, max:int, this: Ref);
ensures (mapOfColleges[this] == m);
ensures	(maxSize[this] == max);

procedure makeMapNull(i : int, this:Ref)
modifies mapOfColleges;
ensures (forall j:int :: ((j<=i) ==> packedIsEntryNull[this, j]));
{
if (i==0) {
	mapOfColleges[this][i] := null;	
} else {
	call makeMapNull(i-1, this);
}
}

procedure containsKey(key1: int, this:Ref) returns (b:bool)
requires packedMapOfCollegesField[this];
requires (fracMapOfCollegesField[this] > 0.0);
//requires this#k MapOfCollegesField()
//ensures (b == true) && (exists c:College ==> (this#k KeyValuePair(key1, c))	 ||
//	(b == false) && (this#k KeyValuePair(key1, null)) 
{
	b := true;
	if (mapOfColleges[this][key1] == null) {
		b := false;	
	} 
}
	
procedure put(key1 : int, college1: Ref, this:Ref) 
modifies mapOfColleges;
requires packedMapOfCollegesField[this];
requires (fracMapOfCollegesField[this] > 0.0);
ensures packedKeyValuePair[this];
ensures	(fracKeyValuePair[this] > 0.0);
{
	mapOfColleges[this][key1] := college1;	
}
	
procedure get(key1:int, this:Ref) returns (c:Ref)
requires packedMapOfCollegesField[this];
requires (fracMapOfCollegesField[this] > 0.0);
ensures packedKeyValuePair[this];
ensures	(fracKeyValuePair[this] > 0.0);
// TODO make sure fraction values are right
//requires this#k MapOfCollegesField()
//ensures this#k KeyValuePair(key1, result)
{
	c := mapOfColleges[this][key1];
}
	
procedure lookup(collegeNumber:int, this:Ref) returns (r:Ref)
modifies mapOfColleges;
requires packedMapOfCollegesField[this];
requires (fracMapOfCollegesField[this] > 0.0);
ensures packedKeyValuePair[this];
ensures	(fracKeyValuePair[this] > 0.0);
//ensures this#k KeyValuePair(collegeNumber, result)
{
var temp:bool;
var c:Ref;
call temp := containsKey(collegeNumber, this);
if (temp == false) 
	{
		call ConstructCollege(collegeNumber, c);
		packedCollegeFields[c] := false;
		call PackCollegeFields(collegeNumber, c);
		packedCollegeFields[c] := true;
		fracCollegeFields[c] := 1.0;

		call put(collegeNumber, c, this);
	}
call r:= get(collegeNumber, this);
}

//--------------------------

var college : [Ref]Ref;
var campusNumber : [Ref]int;
var facilities : [Ref]Ref;

var packedStudentApplicationFields : [Ref]bool;
var fracStudentApplicationFields : [Ref]real;

var packedStudentAppFacilitiesMany : [Ref]bool;
var fracStudentAppFacilitiesMany : [Ref]real;

var packedStudentAppFacilitiesFew : [Ref]bool;
var fracStudentAppFacilitiesFew : [Ref]real;

procedure PackStudentApplicationFields(c:Ref, camp:int, this:Ref);
requires packedStudentApplicationFields[this] == false;
requires (college[this] == c);
requires (campusNumber[this] == camp);

procedure UnpackStudentApplicationFields(c:Ref, camp:int, this:Ref);
requires packedStudentApplicationFields[this];
ensures (college[this] == c);
ensures	(campusNumber[this] == camp);

procedure PackStudentAppFacilitiesMany(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires packedCollegeFacilitiesMany[col];
requires (fracCollegeFacilitiesMany[col] > 0.0);
//TODO add ensures about params in this object proposition

procedure UnpackStudentAppFacilitiesMany(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this];
requires fracStudentAppFacilitiesMany[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesMany[col];
ensures	(fracCollegeFacilitiesMany[col] > 0.0);

procedure PackStudentAppFacilitiesFew(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires packedCollegeFacilitiesFew[col];
requires (fracCollegeFacilitiesFew[col] > 0.0);
//TODO add ensures about params in this object proposition

procedure UnpackStudentAppFacilitiesFew(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this];
requires fracStudentAppFacilitiesFew[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesFew[col];
ensures	(fracCollegeFacilitiesFew[col] > 0.0);

procedure ConstructStudentApplication(col:Ref, campusNum:int, this:Ref) 
modifies college, facilities, campusNumber;
{
    var temp: int;
		college[this] := col;
		call temp := getNumberFacilities(campusNum, college[this]);
    facilities[this] := temp;
		campusNumber[this] := campusNum;	
}
	
procedure changeApplicationFew(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities;
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
{
  var temp:int;
	campusNumber[this] := modulo(newCampusNumber, 4);
	call temp := getNumberFacilities(campusNumber[this], college[this]);
  facilities[this] := temp;
}

procedure changeApplicationMany(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities;
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
{
  	var temp:int;
	campusNumber[this] := newCampusNumber * 10 + 1;
	call temp := getNumberFacilities(campusNumber[this], college[this]);
  	facilities[this] := temp;
}


procedure checkFacilitiesFew(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
{        
	var temp:bool;
	call temp := getValueInt(facilities[this]);
	b := (temp <= 4 * campusNumber[this]);
}

procedure checkFacilitiesMany(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
{       
	var temp:bool;
	call temp := getValueInt(facilities[this]);
	b := (temp >= 10 * campusNumber[this]);
}


//-------------------------

// Each ApplicationWebsite has its own map of college
// I use mapOfColleges from mapcollege.bpl
//var mapOfAvailableColleges : [Ref]MapIntCollege;

var packedApplicationWebsiteField : [Ref]bool;
var fracApplicationWebsiteField : [Ref]real;

procedure PackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires (packedApplicationWebsiteField[this]==false);
requires (mapOfColleges[this] == m); 

procedure UnpackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires packedApplicationWebsiteField[this];
requires fracApplicationWebsiteField[this] > 0.0;
ensures	(mapOfColleges[this] == m); 

procedure ConstructApplicationWebsite(maxSize1:int, this:Ref)
ensures (fracApplicationWebsiteField[this] == 1.0);

{
	call ConstructMapCollege(mapOfColleges[this], maxSize1, this);	
}

procedure submitApplicationGetCollege(collegeNumber:int, this:Ref) returns (r: Ref)
modifies mapOfColleges;
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
ensures ( packedCollegeBuildingsFew[r] && 
	(fracCollegeBuildingsFew[r] > 0.0) ) ||
	( packedCollegeBuildingsMany[r] &&
	(fracCollegeBuildingsMany[r] > 0.0) );
{
	var college : Ref;
	call college := lookup(collegeNumber, mapOfColleges[this]);
	// might be able to say var r : Ref from the beginning
	r := college;
}

procedure main(this:Ref) 
modifies mapOfColleges;
{
	var website : Ref;
	var college, college2 : Ref;
	var app1, app2 : Ref;
	var app3, app4 : Ref;
  var tempbo : bool;
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

	call tempbo := checkFacilitiesFew(app1);
	call changeApplicationFew(34, app1);
	call tempbo := checkFacilitiesFew(app2);

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

	call tempbo := checkFacilitiesMany(app3);
	call changeApplicationFew(78, app3);
	call tempbo := checkFacilitiesMany(app4);
}
