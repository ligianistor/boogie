//college.bpl

type Ref;
const null: Ref;

var collegeNumber :[Ref]int;
var endowment : [Ref]int;

var packedCollegeNumberField : [Ref]bool;
var fracCollegeNumberField : [Ref]real;

var packedCollegeFacilitiesMany : [Ref]bool;
var fracCollegeFacilitiesMany : [Ref]real;

var packedCollegeFacilitiesFew : [Ref]bool;
var fracCollegeFacilitiesFew : [Ref]real;

procedure PackCollegeNumberField(c: int, this:Ref);
requires (packedCollegeNumberField[this]==false);
requires (collegeNumber[this] == c); 
requires c>0;

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
requires fracCollegeNumberField[this] > 0.0;
requires (collegeNumber[this] == c);
ensures c>0;

procedure PackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesMany[this] == false);
requires fracCollegeNumberField[this] > 0.0;
requires (collegeNumber[this] == colNum);
requires (numFacilities >= 10 * colNum);

procedure UnpackCollegeFacilitiesMany(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesMany[this];
requires fracCollegeFacilitiesMany[this] > 0.0;
requires (collegeNumber[this] == colNum);
ensures	(numFacilities >= 10 * colNum);

procedure PackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires (packedCollegeFacilitiesFew[this] == false);
requires fracCollegeNumberField[this] > 0.0;
requires (collegeNumber[this] == colNum);
requires (numFacilities <= 4 * colNum);

procedure UnpackCollegeFacilitiesFew(numFacilities:int, colNum:int, this:Ref);
requires packedCollegeFacilitiesFew[this];
requires fracCollegeFacilitiesFew[this] > 0.0;
requires (collegeNumber[this] == colNum);
ensures	(numFacilities <= 4 * colNum);

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

procedure ConstructCollege(number:int, this:Ref) 
modifies collegeNumber, endowment;
//ensures packedCollegeNumberField[this];
ensures (collegeNumber[this] == number);
{
	collegeNumber[this] := number;
	endowment[this] := (number *1000) - 5;
}

procedure getCollegeNumber(c:int, this:Ref) returns (r:int)
modifies packedCollegeNumberField;
requires packedCollegeNumberField[this];
requires collegeNumber[this] == c;
requires (fracCollegeNumberField[this] > 0.0);
ensures packedCollegeNumberField[this];
ensures	(fracCollegeNumberField[this] > 0.0);
ensures collegeNumber[this] == c;
{
	call UnpackCollegeNumberField(c, this);
	packedCollegeNumberField[this] := false;
	r := c;
	call PackCollegeNumberField(collegeNumber[this], this);
	packedCollegeNumberField[this] := true;
}

// the method that calculates the extrinsic state
procedure getNumberFacilities(campNum:int, colNum:int, this:Ref) returns (r:int)
modifies packedCollegeNumberField;
requires packedCollegeNumberField[this];
requires fracCollegeNumberField[this] > 0.0;
requires (collegeNumber[this] == colNum);
requires campNum > 0;
requires colNum > 0;
ensures  r == colNum * campNum;
{
	call UnpackCollegeNumberField(colNum, this);
	packedCollegeNumberField[this] := false;
	r := colNum * campNum;
	call PackCollegeNumberField(colNum, this);
	packedCollegeNumberField[this] := true;
}

//---------------------------
//studentapplication.bpl

var college : [Ref]Ref;
var campusNumber : [Ref]int;
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
requires (college[this] == c);
requires (campusNumber[this] == camp);

procedure PackStudentAppFacilitiesMany(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires (fracCollegeFacilitiesMany[col] > 0.0);
requires fa >= 10 * collegeNumber[col];

procedure UnpackStudentAppFacilitiesMany(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this];
requires fracStudentAppFacilitiesMany[this] > 0.0;
requires (college[this] == col);
requires (campusNumber[this] == c);
ensures	(fracCollegeFacilitiesMany[col] > 0.0);
ensures fa >= 10 * collegeNumber[col];

procedure PackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires (fracCollegeFacilitiesFew[col] > 0.0);
requires fa <= 4 * collegeNumber[col];

procedure UnpackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this];
requires fracStudentAppFacilitiesFew[this] > 0.0;
requires (college[this] == col);
requires (campusNumber[this] == c);
ensures	(fracCollegeFacilitiesFew[col] > 0.0);
ensures fa <= 4 * collegeNumber[col];

procedure ConstructStudentApplication(col:Ref, campusNum:int, this:Ref) 
modifies college, facilities, campusNumber, 
        packedCollegeFacilitiesFew, packedCollegeFacilitiesMany,
        fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
        packedCollegeNumberField;
requires campusNum > 0;
requires packedCollegeNumberField[col];
requires fracCollegeNumberField[col] > 0.0;
requires collegeNumber[col] > 0;
ensures (college[this] == col);
ensures (campusNumber[this] == campusNum);
ensures ( (campusNum <= 4) && (campusNum > 0)  )==> ( packedCollegeFacilitiesFew[col] && 
	(fracCollegeFacilitiesFew[col] > 0.0)  && (facilities[this] == collegeNumber[col] * campusNum) );
ensures (campusNum >= 10) ==> ( packedCollegeFacilitiesMany[col] &&
	(fracCollegeFacilitiesMany[col] > 0.0)  && (facilities[this] == collegeNumber[col] * campusNum) );
// The ensures here are because the variables of type College can satisfy either packedCollegeFacilitiesFew or packedCollegeFacilitiesMany.
// This is an artifact of Boogie, if we could specify more granular "modifies" clauses then we wouldn't need all these ensures forall or 
// requires forall.
// The alternative would be to have a constructor ConstructStudentApplication that constructs a College with many facilities and
// another constructor for a College with few facilities.
ensures  (forall  x:Ref :: ( old(packedCollegeFacilitiesFew[x]) == true ==> packedCollegeFacilitiesFew[x]));
ensures  (forall  x:Ref :: ( old(packedCollegeFacilitiesMany[x]) == true ==>  packedCollegeFacilitiesMany[x]));
{
    var temp : int;
    college[this] := col;
    call temp := getNumberFacilities(campusNum, collegeNumber[col], col);
    facilities[this] := temp;// !!!Here I need to add in the Java program what is the
    // new predicate that has to hold about col, because only now I have all the information
    // to know which predicate holds.
    // I have a fraction to col since it is given as input.
    campusNumber[this] := campusNum;	
    if (0 < campusNum  && campusNum <= 4) {
      packedCollegeFacilitiesFew[col] := false;
      call PackCollegeFacilitiesFew(facilities[this], collegeNumber[col], col);
      packedCollegeFacilitiesFew[col] := true;
      fracCollegeFacilitiesFew[col] := fracCollegeNumberField[col];
    } else if (campusNum >= 10) {
      packedCollegeFacilitiesMany[col] := false;
      call PackCollegeFacilitiesMany(facilities[this] ,collegeNumber[col], col);
      packedCollegeFacilitiesMany[col] := true;
      fracCollegeFacilitiesMany[col] := fracCollegeNumberField[col];
    } else {
      // we cannot end up here
      assume false;
    }
}

procedure changeApplicationFew(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities, 
        packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany, packedCollegeNumberField,
        fracCollegeNumberField;
requires newCampusNumber > 0;
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
requires (forall  x:Ref :: ( packedCollegeFacilitiesFew[x]));
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
ensures (forall y:Ref :: ( (y!=this) ==> (packedStudentAppFacilitiesFew[y] == old(packedStudentAppFacilitiesFew[y]) ) ) );
{
	var temp : int;
	call UnpackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
	packedStudentAppFacilitiesFew[this] := false;
	campusNumber[this] := (newCampusNumber - int(newCampusNumber/4)*4) + 1; 
	call temp := getNumberFacilities(campusNumber[this], collegeNumber[college[this]], college[this]);
  	facilities[this] := temp;
  	call PackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
  	packedStudentAppFacilitiesFew[this] := true;
}

procedure changeApplicationMany(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities,
      packedCollegeNumberField, packedStudentAppFacilitiesMany, fracCollegeNumberField;
requires newCampusNumber > 0;
requires packedStudentAppFacilitiesMany[this];
requires (fracStudentAppFacilitiesMany[this] > 0.0);
requires (forall  x:Ref :: ( packedCollegeFacilitiesMany[x]));
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
ensures (forall y:Ref :: ( (y!=this) ==> (packedStudentAppFacilitiesMany[y] == old(packedStudentAppFacilitiesMany[y]) ) ) );
{
	var temp:int; 
    	call UnpackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
    	packedStudentAppFacilitiesMany[this] := false;
	campusNumber[this] := newCampusNumber * 10 + 1;
	call temp := getNumberFacilities(campusNumber[this],collegeNumber[college[this]], college[this]);
  	facilities[this] := temp;
    	call PackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
    	packedStudentAppFacilitiesMany[this] := true;
}

procedure checkFacilitiesFew(this:Ref) returns (b:bool)
modifies packedStudentAppFacilitiesFew;
requires packedStudentAppFacilitiesFew[this];
requires (fracStudentAppFacilitiesFew[this] > 0.0);
requires (forall y:Ref :: ( packedStudentAppFacilitiesFew[y]));
ensures packedStudentAppFacilitiesFew[this];
ensures	(fracStudentAppFacilitiesFew[this] > 0.0);
ensures (forall y:Ref :: ( packedStudentAppFacilitiesFew[y]));
{        
	call UnpackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
	packedStudentAppFacilitiesFew[this] := false;
	b := (facilities[this] <= 4 * campusNumber[this]);
	call PackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
	packedStudentAppFacilitiesFew[this] := true;
}

procedure checkFacilitiesMany(this:Ref) returns (b:bool)
modifies packedStudentAppFacilitiesMany;
requires packedStudentAppFacilitiesMany[this];
requires (forall y:Ref :: ( packedStudentAppFacilitiesMany[y]));
requires (fracStudentAppFacilitiesMany[this] > 0.0);
ensures packedStudentAppFacilitiesMany[this];
ensures	(fracStudentAppFacilitiesMany[this] > 0.0);
ensures (forall y:Ref :: ( packedStudentAppFacilitiesMany[y]));
{       
	call UnpackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
	packedStudentAppFacilitiesMany[this] := false;
	b := (facilities[this] >= 10 * campusNumber[this]);
	call PackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
	packedStudentAppFacilitiesMany[this] := true;
}

//-------------------------
//applicationwebsite.bpl

type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.

var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;

var packedMapOfCollegesField : [Ref]bool;
var fracMapOfCollegesField : [Ref]real;

// Each ApplicationWebsite has its own map of college

var packedApplicationWebsiteField : [Ref]bool;
var fracApplicationWebsiteField : [Ref]real;

procedure PackMapOfCollegesField(m: MapIntCollege, this:Ref);
requires (packedMapOfCollegesField[this]==false);
requires (mapOfColleges[this] == m); 

procedure UnpackMapOfCollegesField(m: MapIntCollege, this:Ref);
requires packedMapOfCollegesField[this];
requires fracMapOfCollegesField[this] > 0.0;
requires (mapOfColleges[this] == m); 


procedure PackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires (packedApplicationWebsiteField[this]==false);
requires (mapOfColleges[this] == m); 
requires  (forall j:int :: (  ((j<=maxSize[this]) && (j>=0)) ==> 
           packedKeyValuePair[this, j] && (fracKeyValuePair[this, j] > 0.0) ) );

procedure UnpackApplicationWebsiteField(m: MapIntCollege, this:Ref);
requires packedApplicationWebsiteField[this];
requires fracApplicationWebsiteField[this] > 0.0;
requires (mapOfColleges[this] == m);
ensures  (forall j:int :: (  ((j<=maxSize[this]) && (j>=0)) ==> 
           packedKeyValuePair[this, j] && (fracKeyValuePair[this, j] > 0.0) ) );

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index, the key, 
// that we need in order to get to the value.
var packedKeyValuePair : [Ref, int]bool;
var fracKeyValuePair : [Ref, int]real;

procedure PackKeyValuePair(key:int, value:Ref, m:MapIntCollege, this:Ref);
requires packedKeyValuePair[this, key] == false;
requires fracMapOfCollegesField[this] > 0.0;
requires mapOfColleges[this] == m;
requires (m[key] == value);

procedure UnpackKeyValuePair(key:int, value:Ref, m:MapIntCollege, this:Ref);
requires packedKeyValuePair[this, key];
requires fracKeyValuePair[this, key] > 0.0;
requires (mapOfColleges[this] == m);
ensures (m[key] == value);

procedure makeMapNull(i : int, this:Ref)
modifies mapOfColleges, packedKeyValuePair, fracKeyValuePair, packedMapOfCollegesField;
requires (i>=0);
ensures (forall j:int :: (((j<=i) && (j>=0) ) ==> (packedKeyValuePair[this, j] && ( fracKeyValuePair[this, j] == 1.0 )))  );
{
if (i==0) {
	mapOfColleges[this][i] := null;	
	call PackMapOfCollegesField(mapOfColleges[this], this);
	packedMapOfCollegesField[this] := true;
	call PackKeyValuePair(i, null, mapOfColleges[this], this);
  	packedKeyValuePair[this, i] := true;
  	fracKeyValuePair[this, i] := 1.0;
} else if (i>0) {
	call makeMapNull(i-1, this);
  	mapOfColleges[this][i] := null;	
	call PackMapOfCollegesField(mapOfColleges[this], this);
	packedMapOfCollegesField[this] := true;
	call PackKeyValuePair(i, null, mapOfColleges[this], this);
  	packedKeyValuePair[this, i] := true;
  	fracKeyValuePair[this, i] := 1.0;
}
}

procedure containsKey(key1: int, this:Ref) returns (b:bool)
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
//requires this#k MapOfCollegesField()
ensures (b == true) ==> packedKeyValuePair[this, key1] && (fracKeyValuePair[this, key1] > 0.0);
ensures (b == false) ==> packedKeyValuePair[this, key1] && (fracKeyValuePair[this, key1] > 0.0) &&(mapOfColleges[this][key1] == null);
{
	b := true;
	if (mapOfColleges[this][key1] == null) {
		b := false;	
	} 
}
	
procedure put(key1 : int, college1: Ref, this:Ref) 
modifies mapOfColleges, packedKeyValuePair, packedMapOfCollegesField;
requires packedApplicationWebsiteField[this]==false;
requires (fracApplicationWebsiteField[this] > 0.0);
// This put procedure will be called with null for the value in packedKeyValuePair.
requires packedKeyValuePair[this, key1];
requires (fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
{
	call UnpackKeyValuePair(key1, null, mapOfColleges[this], this);
	packedKeyValuePair[this, key1] := false;
	call UnpackMapOfCollegesField(mapOfColleges[this], this);
	packedMapOfCollegesField[this] := false;
	mapOfColleges[this][key1] := college1;
	call PackMapOfCollegesField(mapOfColleges[this], this);
	packedMapOfCollegesField[this] := true;	
	call PackKeyValuePair(key1, college1, mapOfColleges[this], this);
	packedKeyValuePair[this, key1] := true;
 }
	
procedure get(key1:int, this:Ref) returns (c:Ref)
requires packedKeyValuePair[this, key1];
requires (fracKeyValuePair[this, key1] > 0.0);
ensures packedKeyValuePair[this, key1];
ensures	(fracKeyValuePair[this, key1] > 0.0);
ensures packedCollegeNumberField[c];
ensures fracCollegeNumberField[c] > 0.0;
//requires this#k MapOfCollegesField()
//ensures this#k KeyValuePair(key1, result)
{
	c := mapOfColleges[this][key1];
}
	
procedure lookup(colNum:int, this:Ref) returns (r:Ref)
modifies mapOfColleges, packedCollegeNumberField, fracCollegeNumberField,collegeNumber,
       endowment, packedKeyValuePair, packedApplicationWebsiteField, packedMapOfCollegesField;
requires (0<colNum);
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
ensures packedKeyValuePair[this, colNum];
ensures	(fracKeyValuePair[this, colNum] > 0.0);
ensures packedCollegeNumberField[r];
ensures fracCollegeNumberField[r] > 0.0;

//ensures this#k KeyValuePair(colNum, result)
{
	var temp:bool;
	var c:Ref;
	call temp := containsKey(colNum, this);
	call UnpackApplicationWebsiteField(mapOfColleges[this], this);
	packedApplicationWebsiteField[this]:=false;
	if (temp == false) {
		call ConstructCollege(colNum, c);
		packedCollegeNumberField[c] := false;
		call PackCollegeNumberField(colNum, c);
		packedCollegeNumberField[c] := true;
		fracCollegeNumberField[c] := 1.0;
	    
		call put(colNum, c, this);
	}
	call r:= get(colNum, this);
}

procedure ConstructApplicationWebsite(maxSize1:int, this:Ref)
modifies maxSize, mapOfColleges, packedKeyValuePair, fracKeyValuePair, packedMapOfCollegesField;
requires (maxSize1>=0);
ensures (forall j:int :: ((j<=maxSize1) && (j>=0)) ==> (packedKeyValuePair[this, j] && (fracKeyValuePair[this, j]==1.0)) ) ;
ensures maxSize[this] == maxSize1;
{
	call makeMapNull(maxSize1, this);
	maxSize[this] := maxSize1;
}

procedure submitApplicationGetCollege(colNum:int, this:Ref) returns (r: Ref)
modifies mapOfColleges, packedCollegeNumberField, fracCollegeNumberField, collegeNumber, endowment,
        packedKeyValuePair, packedApplicationWebsiteField, packedMapOfCollegesField;
requires packedApplicationWebsiteField[this];
requires (fracApplicationWebsiteField[this] > 0.0);
requires (0<colNum);
ensures packedCollegeNumberField[r];
ensures fracCollegeNumberField[r] > 0.0;
{
	call r := lookup(colNum, this);
  
}

procedure main1(this:Ref) 
modifies mapOfColleges, packedApplicationWebsiteField,
  packedStudentAppFacilitiesFew, packedStudentAppFacilitiesMany,
  packedCollegeNumberField, fracCollegeNumberField, collegeNumber, endowment,
  fracApplicationWebsiteField, college, facilities, campusNumber, 
  fracStudentAppFacilitiesFew,
  fracStudentAppFacilitiesMany, maxSize, 
  fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
  packedKeyValuePair, fracKeyValuePair,
  packedCollegeFacilitiesFew, packedCollegeFacilitiesMany, packedCollegeNumberField,
  fracCollegeNumberField, packedMapOfCollegesField;
requires (forall  x:Ref :: ( packedCollegeFacilitiesFew[x]));
requires (forall y:Ref :: ( packedStudentAppFacilitiesFew[y]));
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

 	call UnpackCollegeNumberField(collegeNumber[college], college);
 	packedCollegeNumberField[college] := false;
	call ConstructStudentApplication(college, 3, app1);

	packedStudentAppFacilitiesFew[app1] := false;
	call PackStudentAppFacilitiesFew(facilities[app1], college, 3, app1);
	packedStudentAppFacilitiesFew[app1] := true;
	fracStudentAppFacilitiesFew[app1] := 1.0;
	fracCollegeFacilitiesFew[college] := fracCollegeFacilitiesFew[college] / 2.0;

 	//transfer
  
   	call UnpackCollegeNumberField(collegeNumber[college], college);
    	packedCollegeNumberField[college] := false;
	call ConstructStudentApplication(college, 2, app2);
	packedStudentAppFacilitiesFew[app2] := false;
	call PackStudentAppFacilitiesFew(facilities[app2], college, 2, app2);
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
  fracStudentAppFacilitiesFew,
  fracStudentAppFacilitiesMany, maxSize,
  fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
  packedKeyValuePair, fracKeyValuePair,
  packedCollegeFacilitiesFew, packedCollegeFacilitiesMany,
  packedCollegeNumberField, fracCollegeNumberField, packedMapOfCollegesField;
requires (forall  x:Ref :: ( packedCollegeFacilitiesMany[x]));
requires (forall y:Ref :: ( packedStudentAppFacilitiesMany[y]));
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

   	call UnpackCollegeNumberField(collegeNumber[college2], college2);
    	packedCollegeNumberField[college2] := false;
	call ConstructStudentApplication(college2, 45, app3);

	packedStudentAppFacilitiesMany[app3] := false;
  
	call PackStudentAppFacilitiesMany(facilities[app3], college2, 45, app3);
	packedStudentAppFacilitiesMany[app3] := true;
	fracStudentAppFacilitiesMany[app3] := 1.0;
	fracCollegeFacilitiesMany[college2] := fracCollegeFacilitiesMany[college2] / 2.0;
  
   	//transfer


   	call UnpackCollegeNumberField(collegeNumber[college2], college2);
    	packedCollegeNumberField[college2] := false;
	call ConstructStudentApplication(college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := false;
	call PackStudentAppFacilitiesMany(facilities[app4], college2, 97, app4);
	packedStudentAppFacilitiesMany[app4] := true;
	fracStudentAppFacilitiesMany[app4] := 1.0;
	fracCollegeFacilitiesMany[college2] := fracCollegeFacilitiesMany[college2] / 2.0;

	call tempbo := checkFacilitiesMany(app3);
	call changeApplicationMany(78, app3);
  
	call tempbo := checkFacilitiesMany(app4);
}
