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

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
requires fracCollegeNumberField[this] > 0.0;
ensures	(collegeNumber[this] == c);

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
ensures  r == colNum * campNum;
ensures r> 0;
{
	r := colNum * campNum;
}
