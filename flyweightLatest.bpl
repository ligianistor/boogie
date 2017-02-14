//intcell.bpl
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

procedure getValueInt(this: Ref) returns (r:int)
{
	r := value[this];
}

//-------------------
//college.bpl

var collegeNumber :[Ref]int;
var endowment : [Ref]int;
var facilitiesCol : [Ref]int;

var packedCollegeNumberField : [Ref]bool;
var fracCollegeNumberField : [Ref]real;

var packedCollegeFacilitiesMany : [Ref]bool;
var fracCollegeFacilitiesMany : [Ref]real;

var packedCollegeFacilitiesFew : [Ref]bool;
var fracCollegeFacilitiesFew : [Ref]real;

procedure PackCollegeNumberField(c: int, this:Ref);
requires (packedCollegeNumberField[this]==false);
requires (collegeNumber[this] == c); 

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
requires fracCollegeNumberField[this] > 0.0;
ensures	(collegeNumber[this] == c);

procedure PackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesMany[this] == false);
requires (collegeNumber[this] == colNum);
requires (facilitiesCol[this] == numFacilities);
requires (numFacilities >= 10 * colNum);

procedure UnpackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesMany[this];
requires fracCollegeFacilitiesMany[this] > 0.0;
ensures (collegeNumber[this] == colNum);
ensures (facilitiesCol[this] == numFacilities);
ensures	(numFacilities >= 10 * colNum);

procedure PackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesFew[this] == false);
requires (collegeNumber[this] == colNum);
requires (facilitiesCol[this] == numFacilities);
requires (numFacilities <= 4 * colNum);

procedure UnpackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesFew[this];
requires fracCollegeFacilitiesFew[this] > 0.0;
ensures (collegeNumber[this] == colNum);
ensures (facilitiesCol[this] == numFacilities);
ensures	(numFacilities <= 4 * colNum);

procedure ConstructCollege(number:int, this:Ref) 
modifies collegeNumber, endowment;
// Only for Construct we don't need the packed below. 
// For the other procedures we do need to say about packed.
//ensures packedCollegeNumberField[this];
ensures (collegeNumber[this] == number);
// TODO need to put in statements about the parameters.
// ensures this#k CollegeNumberField()[number]
{
	collegeNumber[this] := number;
	endowment[this] := (number *1000) - 5;
}

procedure getCollegeNumber(this:Ref) returns (r:int)
modifies packedCollegeNumberField;
requires packedCollegeNumberField[this];
requires (fracCollegeNumberField[this] > 0.0);
ensures packedCollegeNumberField[this];
ensures	(fracCollegeNumberField[this] > 0.0);
// TODO add statement about value of parameter 
// ensures this#k CollegeNumberField()[result]
{
	call UnpackCollegeNumberField(collegeNumber[this], this);
	packedCollegeNumberField[this] := false;
	r := collegeNumber[this];
	call PackCollegeNumberField(collegeNumber[this], this);
	packedCollegeNumberField[this] := true;
}

// the method that calculates the extrinsic state
procedure getNumberFacilities(campNum:int, colNum:int, this:Ref) returns (r:int)
modifies divider, value;
requires packedCollegeNumberField[this] == false;
requires fracCollegeNumberField[this] > 0.0;
  requires (collegeNumber[this] == colNum);
  requires campNum > 0;
  requires colNum > 0;
  //TODO add an or of packed[] == false
//requires packedCollegeNumberField[this]==false; 
// I should add || packedCollegeFacilitiesMany == false 
// || packedCollegeFacilitiesFew ==false
//requires (fracCollegeNumberField[this] > 0.0);
//TODO add ensures about the parameters
ensures  r == colNum * campNum;
ensures r> 0;
{
	r := colNum * campNum;
}

//---------------------------
//studentapplication.bpl

var college : [Ref]Ref;
var campusNumber : [Ref]int;
// facilities is a field of StudentApplication
var facilities : [Ref]int;

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

procedure PackStudentAppFacilitiesMany(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires packedCollegeFacilitiesMany[col];
requires (fracCollegeFacilitiesMany[col] > 0.0);

procedure UnpackStudentAppFacilitiesMany(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this];
requires fracStudentAppFacilitiesMany[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesMany[col];
ensures	(fracCollegeFacilitiesMany[col] > 0.0);

procedure PackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires packedCollegeFacilitiesFew[col];
requires (fracCollegeFacilitiesFew[col] > 0.0);

procedure UnpackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this];
requires fracStudentAppFacilitiesFew[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesFew[col];
ensures	(fracCollegeFacilitiesFew[col] > 0.0);

procedure ConstructStudentApplication(col:Ref, campusNum:int, this:Ref) 
modifies college, facilities, campusNumber, fracMultipleOf, packedMultipleOf, divider, value,
        packedCollegeFacilitiesFew, packedCollegeFacilitiesMany
        , fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
        packedCollegeNumberField;
  requires campusNum > 0;
  requires packedCollegeNumberField[col];
  requires fracCollegeNumberField[col] > 0.0;
  ensures (college[this] == col);
  ensures (campusNumber[this] == campusNum);
  ensures ( (campusNum <= 4) && (campusNum > 0)  )==> ( packedCollegeFacilitiesFew[col] && 
	(fracCollegeFacilitiesFew[col] > 0.0) );
  ensures (campusNum >= 10) ==> ( packedCollegeFacilitiesMany[col] &&
	(fracCollegeFacilitiesMany[col] > 0.0) );
{
    var temp : int;
    assume (forall y:Ref :: (collegeNumber[y] > 0) );
		college[this] := col;
    call UnpackCollegeNumberField(collegeNumber[college[this]], college[this]);
    packedCollegeNumberField[college[this]] := false;
		call temp := getNumberFacilities(campusNum, collegeNumber[college[this]], college[this]);
    facilities[this] := temp;// !!!Here I need to add in the Java program what is the
    // new predicate that has to hold about col, because only now I have all the information
    // to know which predicate holds.
    // I have a fraction to col since it is given as input.
		campusNumber[this] := campusNum;	
    if (0 < campusNum  && campusNum <= 4) {
      packedCollegeFacilitiesFew[college[this]] := false;
      call PackCollegeFacilitiesFew(facilities[this], collegeNumber[college[this]], college[this]);
      packedCollegeFacilitiesFew[college[this]] := true;
      fracCollegeFacilitiesFew[college[this]] := 0.001;
      
    } else if (campusNum >= 10) {
      packedCollegeFacilitiesMany[college[this]] := false;
      call PackCollegeFacilitiesMany(facilities[this] ,collegeNumber[college[this]], college[this]);
      packedCollegeFacilitiesMany[college[this]] := true;
      fracCollegeFacilitiesMany[college[this]] := 0.001;
    } else {
      // we cannot end up here
      assume false;
    }
}

procedure changeApplicationFew(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities, fracMultipleOf, packedMultipleOf, divider, value,
        packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany, packedCollegeNumberField,
        fracCollegeNumberField;
requires newCampusNumber > 0;
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
ensures (forall y:Ref :: ( (y!=this) ==> (packedStudentAppFacilitiesFew[y] == old(packedStudentAppFacilitiesFew[y]) ) ) );
{
  var temp : int;
  assume (forall y:Ref :: (collegeNumber[y] > 0) );
  call UnpackStudentAppFacilitiesFew(college[this], campusNumber[this], this);
  packedStudentAppFacilitiesFew[this] := false;
	campusNumber[this] := modulo(newCampusNumber, 4) + 1;
    
    //transfer
    packedCollegeNumberField[college[this]] := packedCollegeFacilitiesFew[college[this]];
    fracCollegeNumberField[college[this]] := fracCollegeFacilitiesFew[college[this]];

    call UnpackCollegeNumberField(collegeNumber[college[this]], college[this]);
    packedCollegeNumberField[college[this]] := false;
	call temp := getNumberFacilities(campusNumber[this], collegeNumber[college[this]], college[this]);
  facilities[this] := temp;
  call PackStudentAppFacilitiesFew(college[this], campusNumber[this], this);
  packedStudentAppFacilitiesFew[this] := true;
}

procedure changeApplicationMany(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities, fracMultipleOf, packedMultipleOf, divider, value,
      packedCollegeNumberField, packedStudentAppFacilitiesMany, fracCollegeNumberField;
requires newCampusNumber > 0;
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
ensures (forall y:Ref :: ( (y!=this) ==> (packedStudentAppFacilitiesMany[y] == old(packedStudentAppFacilitiesMany[y]) ) ) );
{
  	var temp:int; 
    assume (forall y:Ref :: (collegeNumber[y] > 0) );
    call UnpackStudentAppFacilitiesMany(college[this], campusNumber[this], this);
    packedStudentAppFacilitiesMany[this] := false;
	  campusNumber[this] := newCampusNumber * 10 + 1;
    
    //transfer
    packedCollegeNumberField[college[this]] := packedCollegeFacilitiesMany[college[this]];
    fracCollegeNumberField[college[this]] := fracCollegeFacilitiesMany[college[this]];

    call UnpackCollegeNumberField(collegeNumber[college[this]], college[this]);
    packedCollegeNumberField[college[this]] := false;
	  call temp := getNumberFacilities(campusNumber[this],collegeNumber[college[this]], college[this]);
  	facilities[this] := temp;
    call PackStudentAppFacilitiesMany(college[this], campusNumber[this], this);
    packedStudentAppFacilitiesMany[this] := true;
}

procedure checkFacilitiesFew(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
{        
	b := (facilities[this] <= 4 * campusNumber[this]);
}

procedure checkFacilitiesMany(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
{       
	b := (facilities[this] >= 10 * campusNumber[this]);
}


//-------------------------
//applicationwebsite.bpl

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
