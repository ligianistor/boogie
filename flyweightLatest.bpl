type Ref;
const null: Ref;

var value: [Ref]int;
var divider : [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedBasicIntCell: [Ref] bool;
var fracBasicIntCell: [Ref] real;

var packedIntCellMany : [Ref] bool;
var fracIntCellMany : [Ref]real;

var packedIntCellFew : [Ref] bool;
var fracIntCellFew : [Ref]real;

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
requires ( (v - int(v/a)*a )==0);

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);
ensures	 ( (v - int(v/a)*a )==0);

//TODO need to fix the body of this
procedure PackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires (packedIntCellMany[this]==false);
requires (value[this] == val);
requires (divider[this] == divi);
requires (quot >= 10);

procedure UnpackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires packedIntCellMany[this];
requires fracIntCellMany[this] > 0.0;
ensures	(value[this] == val);
ensures (divider[this] == divi);
ensures (quot >= 10);

procedure PackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires (packedIntCellFew[this]==false);
requires (value[this] == v);
requires (divider[this] == divi);
requires (quot <= 4);

procedure UnpackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires packedIntCellFew[this];
requires fracIntCellFew[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == divi);
ensures (quot <= 4);

procedure ConstructIntCell(divider1: int, value1: int, this: Ref)
modifies divider, value;
ensures (value[this] == value1);
ensures (divider[this] == divider1);
{
	value[this] := value1;
	divider[this] := divider1;
}

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

procedure UnpackCollegeFields(colNum:int, this:Ref);
requires packedCollegeFields[this];
requires fracCollegeFields[this] > 0.0;
ensures	(collegeNumber[this] == colNum);
ensures (endowment[this] == colNum*1000 - 5);

procedure PackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesMany[this] == false);
requires (collegeNumber[this] == colNum);
requires (numFacilities >= 10 * colNum);

procedure UnpackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesMany[this];
requires fracCollegeFacilitiesMany[this] > 0.0;
ensures (collegeNumber[this] == colNum);
ensures	(numFacilities >= 10 * colNum);

procedure PackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesFew[this] == false);
requires (collegeNumber[this] == colNum);
requires (numFacilities <= 4 * colNum);

procedure UnpackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesFew[this];
requires fracCollegeFacilitiesFew[this] > 0.0;
ensures (collegeNumber[this] == colNum);
ensures	(numFacilities <= 4 * colNum);

procedure ConstructCollege(number:int, this:Ref) 
modifies collegeNumber, endowment;
// Only for Construct we don't need the packed below. 
// For the other procedures we do need to say about packed.
//ensures packedCollegeFields[this];
ensures (collegeNumber[this] == number);
ensures (endowment[this] == (number *1000) - 5);
// TODO need to put in statements about the parameters.
// ensures this#k CollegeFields()[number, (number*1000)-5]
{
	collegeNumber[this] := number;
	endowment[this] := (number *1000) - 5;
}

procedure getCollegeNumber(this:Ref) returns (r:int)
requires packedCollegeNumberField[this];
requires (fracCollegeNumberField[this] > 0.0);
ensures packedCollegeNumberField[this];
ensures	(fracCollegeNumberField[this] > 0.0);
// TODO add statement about value of parameter 
// ensures this#k CollegeNumberField()[result]
{
	r := collegeNumber[this];
}

// the method that calculates the extrinsic state
procedure getNumberFacilities(campNum:int, colNum:int, this:Ref) returns (r:Ref)
modifies divider, value, 
	packedIntCellMany, packedIntCellFew,
  fracIntCellMany, fracIntCellFew;
  requires (collegeNumber[this] == colNum);
  //TODO add an or of packed[] == false
//requires packedCollegeNumberField[this]==false; 
// I should add || packedCollegeFacilitiesMany == false 
// || packedCollegeFacilitiesFew ==false
//requires (fracCollegeNumberField[this] > 0.0);
//TODO add ensures about the parameters
ensures (campNum>=10) ==> (packedIntCellMany[r] && (fracIntCellMany[r]==1.0));
ensures (campNum<=4) ==>  (packedIntCellFew[r] && (fracIntCellFew[r]==1.0));
{
	call ConstructIntCell(collegeNumber[this], collegeNumber[this] * campNum, r);
	if (campNum>=10) {
		packedIntCellMany[r] := false;
		call PackIntCellMany(collegeNumber[this], collegeNumber[this] * campNum,  campNum, r);
		packedIntCellMany[r] := true;
		fracIntCellMany[r] := 1.0;
	} else if (campNum<=4) {
		packedIntCellFew[r] := false;
		call PackIntCellFew(collegeNumber[this], collegeNumber[this] * campNum,  campNum, r);
		packedIntCellFew[r] := true;
		fracIntCellFew[r] := 1.0;
	}	
}

//---------------------------

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
requires packedCollegeNumberField[col];
requires (fracCollegeNumberField[col] > 0.0);
modifies college, facilities, campusNumber, fracMultipleOf, packedMultipleOf, divider, value
        , packedIntCellMany, packedIntCellFew,
        fracIntCellMany, fracIntCellFew;
{
    var temp : Ref;
		college[this] := col;
		call temp := getNumberFacilities(campusNum, collegeNumber[college[this]], college[this]);
    facilities[this] := temp;
		campusNumber[this] := campusNum;	
}
	
procedure changeApplicationFew(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities, fracMultipleOf, packedMultipleOf, divider, value
  , packedIntCellMany, packedIntCellFew,
        fracIntCellMany, fracIntCellFew,
        packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany;
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
{
  var temp : Ref;
	campusNumber[this] := modulo(newCampusNumber, 4);
  call UnpackStudentAppFacilitiesFew(college[this], campusNumber[this], this);
  packedStudentAppFacilitiesFew[this] := false;
	call temp := getNumberFacilities(campusNumber[this], collegeNumber[college[this]], college[this]);
  facilities[this] := temp;
  call PackStudentAppFacilitiesFew(college[this], campusNumber[this], this);
  packedStudentAppFacilitiesFew[this] := true;
}

procedure changeApplicationMany(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities, fracMultipleOf, packedMultipleOf, divider, value
      , packedIntCellMany, packedIntCellFew,
        fracIntCellMany, fracIntCellFew;
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
{
  	var temp:Ref;
	  campusNumber[this] := newCampusNumber * 10 + 1;
	  call temp := getNumberFacilities(campusNumber[this],collegeNumber[college[this]], college[this]);
  	facilities[this] := temp;
}


procedure checkFacilitiesFew(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
{        
	var temp:int;
	call temp := getValueInt(facilities[this]);
	b := (temp <= 4 * campusNumber[this]);
}

procedure checkFacilitiesMany(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
{       
	var temp:int;
	call temp := getValueInt(facilities[this]);
	b := (temp >= 10 * campusNumber[this]);
}


//-------------------------

type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.

var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;

// Each ApplicationWebsite has its own map of college

var packedApplicationWebsiteField : [Ref]bool;
var fracApplicationWebsiteField : [Ref]real;

//TODO I might not need both predicate isEntryNull and KeyValuePair since
// the second one is more general than the first

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

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index, the key, 
// that we need in order to get to the value.
var packedIsEntryNull : [Ref, int]bool;
var fracIsEntryNull : [Ref, int]real;

procedure PackIsEntryNull(key1 : int, m:MapIntCollege, this:Ref);
requires  (packedIsEntryNull[this, key1] == false);
requires (mapOfColleges[this] == m);
requires (m[key1] == null);

procedure UnpackIsEntryNull(key1 : int, m:MapIntCollege, this:Ref);
requires  packedIsEntryNull[this, key1];
ensures (mapOfColleges[this] == m);
ensures (m[key1] == null);

procedure createMapCollege(maxSize1:int, this: Ref)
modifies maxSize, mapOfColleges, packedIsEntryNull, fracIsEntryNull;
requires (maxSize1>=0);
ensures (forall j:int :: ((j<=maxSize1) && (j>=0)) ==> (packedIsEntryNull[this, j] && (fracIsEntryNull[this, j]==1.0)) ) ;
{
maxSize[this] := maxSize1;
call makeMapNull(maxSize1, this);
}

procedure makeMapNull(i : int, this:Ref)
modifies mapOfColleges, packedIsEntryNull, fracIsEntryNull;
requires (i>=0);
ensures (forall j:int :: (((j<=i) && (j>=0) ) ==> (packedIsEntryNull[this, j] && ( fracIsEntryNull[this, j] == 1.0 )))  );
{
if (i==0) {
	mapOfColleges[this][i] := null;	
  packedIsEntryNull[this, i] := true;
  fracIsEntryNull[this, i] := 1.0;
} else if (i>0) {
	call makeMapNull(i-1, this);
  assert (forall j:int :: (((j<=i-1) && (j>=0) ) ==> packedIsEntryNull[this, j]));
  mapOfColleges[this][i] := null;	
  packedIsEntryNull[this, i] := true;
  fracIsEntryNull[this, i] := 1.0;
}
}

procedure containsKey(key1: int, this:Ref) returns (b:bool)
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
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
modifies mapOfColleges, packedKeyValuePair;
//requires packedApplicationWebsiteField[this];
//requires (fracApplicationWebsiteField[this] > 0.0);
// This put procedure will be called with null for the value in packedKeyValuePair.
requires packedKeyValuePair[this, key1];
requires (fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
{
  call UnpackKeyValuePair(mapOfColleges[this], key1, null, this);
  packedKeyValuePair[this, key1] := false;
	mapOfColleges[this][key1] := college1;	
  call PackKeyValuePair(mapOfColleges[this], key1, college1, this);
  packedKeyValuePair[this, key1] := true;
}
	
procedure get(key1:int, this:Ref) returns (c:Ref)
requires packedKeyValuePair[this, key1];
requires	(fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
// TODO make sure fraction values are right
//requires this#k MapOfCollegesField()
//ensures this#k KeyValuePair(key1, result)
{
	c := mapOfColleges[this][key1];
}
	
procedure lookup(collegeNumber:int, this:Ref) returns (r:Ref)
modifies mapOfColleges, packedCollegeFields, fracCollegeFields,collegeNumber,
       endowment, packedKeyValuePair, packedApplicationWebsiteField;
requires (collegeNumber<=maxSize[this]) && (0<=collegeNumber);
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
// TODO needs another requires  related to all fractions in mapOfColleges
// maybe needs to be added in PackApplicationWebsiteField predicate
ensures packedKeyValuePair[this, collegeNumber];
ensures	(fracKeyValuePair[this, collegeNumber] > 0.0);
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
		packedCollegeFields[c] := false;
		call PackCollegeFields(collegeNumber, c);
		packedCollegeFields[c] := true;
		fracCollegeFields[c] := 1.0;
    
		call put(collegeNumber, c, this);
	}
call r:= get(collegeNumber, this);
}

procedure ConstructApplicationWebsite(maxSize1:int, this:Ref)
modifies maxSize, mapOfColleges, packedIsEntryNull, fracIsEntryNull;
requires (maxSize1>=0);
{
	call createMapCollege(maxSize1, this);	
}

procedure submitApplicationGetCollege(collegeNumber:int, this:Ref) returns (r: Ref)
modifies mapOfColleges, packedCollegeFields, fracCollegeFields, collegeNumber, endowment,
        packedKeyValuePair, packedApplicationWebsiteField;
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
requires (collegeNumber<=maxSize[this]) && (0<=collegeNumber);
ensures ( packedCollegeBuildingsFew[r] && 
	(fracCollegeBuildingsFew[r] > 0.0) ) ||
	( packedCollegeBuildingsMany[r] &&
	(fracCollegeBuildingsMany[r] > 0.0) );
{
	call r := lookup(collegeNumber, this);
  // TODO I might need to add the ensures of this function to the ensures of lookup()	
}

procedure main(this:Ref) 
modifies mapOfColleges, packedApplicationWebsiteField,
  packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany,
  packedCollegeFields, fracCollegeFields, collegeNumber, endowment,
  fracApplicationWebsiteField, college, facilities, campusNumber, 
  fracMultipleOf, packedMultipleOf, fracStudentAppFacilitiesFew,
  fracStudentAppFacilitiesMany, maxSize, packedIsEntryNull, divider, value,
  fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
  packedIntCellMany, packedIntCellFew,
  fracIntCellMany, fracIntCellFew,
  fracIsEntryNull, packedKeyValuePair;
{
	var website : Ref;
	var college, college2 : Ref;
	var app1, app2 : Ref;
	var app3, app4 : Ref;
  var tempbo : bool;
	assume (college != college2);
	assume (app1 != app2);
	assume (app3 != app4);
  
  //TODO need to construct mapOfColleges and it needs to ensure that forall
	
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
