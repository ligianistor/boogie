
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
procedure getNumberFacilities(campNum:int, colNum:int, this:Ref) returns (r:int)
modifies divider, value;
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

