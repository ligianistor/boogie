type Ref;
const null: Ref;

var value: [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedMultipleOf21: [Ref] bool;
var fracMultipleOf21: [Ref] real;

var packedMultipleOf16: [Ref] bool;
var fracMultipleOf16: [Ref] real;

var packedMultipleOf15: [Ref] bool;
var fracMultipleOf15: [Ref] real;

var packedMultipleOf14: [Ref] bool;
var fracMultipleOf14: [Ref] real;

var packedMultipleOf33: [Ref] bool;
var fracMultipleOf33: [Ref] real;

var packedMultipleOf4: [Ref] bool;
var fracMultipleOf4: [Ref] real;


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

// TODO maybe need to add a field value that holds a, the one we divide by
procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false);
requires (value[this] == v);
requires (modulo(v,a) == 0); 

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,a) == 0); 

procedure PackMultipleOf21(v:int, this:Ref);
requires (packedMultipleOf21[this]==false);
requires (value[this] == v);
requires (modulo(v,21) == 0); 

procedure UnpackMultipleOf21(v:int, this:Ref);
requires packedMultipleOf21[this];
requires fracMultipleOf21[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,21) == 0); 

procedure PackMultipleOf16(v:int, this:Ref);
requires (packedMultipleOf16[this]==false);
requires (value[this] == v);
requires (modulo(v,16) == 0); 

procedure UnpackMultipleOf16(v:int, this:Ref);
requires packedMultipleOf16[this];
requires fracMultipleOf16[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,16) == 0);

procedure PackMultipleOf15(v:int, this:Ref);
requires (packedMultipleOf15[this]==false);
requires (value[this] == v);
requires (modulo(v,15) == 0); 

procedure UnpackMultipleOf15(v:int, this:Ref);
requires packedMultipleOf15[this];
requires fracMultipleOf15[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,15) == 0);

procedure PackMultipleOf14(v:int, this:Ref);
requires (packedMultipleOf14[this]==false);
requires (value[this] == v);
requires (modulo(v,14) == 0); 

procedure UnpackMultipleOf14(v:int, this:Ref);
requires packedMultipleOf14[this];
requires fracMultipleOf14[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,14) == 0);

procedure PackMultipleOf33(v:int, this:Ref);
requires (packedMultipleOf33[this]==false);
requires (value[this] == v);
requires (modulo(v,33) == 0); 

procedure UnpackMultipleOf33(v:int, this:Ref);
requires packedMultipleOf33[this];
requires fracMultipleOf33[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,33) == 0);

procedure PackMultipleOf4(v:int, this:Ref);
requires (packedMultipleOf4[this]==false);
requires (value[this] == v);
requires (modulo(v,4) == 0); 

procedure UnpackMultipleOf4(v:int, this:Ref);
requires packedMultipleOf4[this];
requires fracMultipleOf4[this] > 0.0;
ensures	(value[this] == v);
ensures	(modulo(v,4) == 0);

procedure ConstructIntCell(x: int, this: Ref);
ensures (value[this] == x);

procedure setValue(x: int, this: Ref) 
modifies value;
{
	value[this] := x;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r:=value[this];
}

//-------------------

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

procedure checkFewFacilities(num:int, this:Ref) returns (b:bool)
requires packedCollegeFacilitiesFew[this];
requires (fracCollegeFacilitiesFew[this] > 0.0);
//requires this#1 collegeFacilitiesFew(num)
ensures packedCollegeFacilitiesFew[this];
ensures	(fracCollegeFacilitiesFew[this] > 0.0);
//ensures this#1 collegeFacilitiesFew(num)
{
	b := (num <= 4 * collegeNumber[this]);
}

procedure checkManyFacilities(num:int, this:Ref) returns (b:bool)
requires packedCollegeFacilitiesMany[this];
requires (fracCollegeFacilitiesMany[this] > 0.0);
//requires this#1 collegeFacilitiesMany(num)
ensures packedCollegeFacilitiesMany[this];
ensures	(fracCollegeFacilitiesMany[this] > 0.0);
//ensures this#1 collegeFacilitiesMany(num)
{
	b := (num >= 10 * collegeNumber[this]);
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

procedure ConstructMapCollege(m: MapIntCollege, max:int, s:int, this: Ref);
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
