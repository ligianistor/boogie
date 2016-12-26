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
requires (packedCollegeNumberField[this]==false) &&
 	(collegeNumber[this] == c); 

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
ensures	(collegeNumber[this] == c);

procedure PackCollegeFields(c: int, e:int, this:Ref);
requires (packedCollegeFields[this]==false) &&
 	(collegeNumber[this] == c) && (endowment[this] == e); 

procedure UnpackCollegeFields(c: int, e:int, this:Ref);
requires packedCollegeFields[this];
ensures	(collegeNumber[this] == c);
ensures (endowment[this] == e);

procedure PackCollegeFacilitiesMany(num:int, c:int, this:Ref);
requires (packedCollegeFacilitiesMany[this] == false);
//TODO all Pack procedures need to refer to frac also, 
// not only to packed.
requires (collegeNumber[this] == c) && (num >= 10 * c);

procedure UnpackCollegeFacilitiesMany(num:int, c:int, this:Ref);
requires packedCollegeFacilitiesMany[this];
//TODO all Unpack procedures need to refer to frac also, 
// not only to packed.
ensures (collegeNumber[this] == c) && (num >= 10 * c);

procedure PackCollegeFacilitiesFew(num:int, c:int, this:Ref);
requires (packedCollegeFacilitiesFew[this] == false);
requires (collegeNumber[this] == c) && (num <= 4 * c);

procedure UnpackCollegeFacilitiesFew(num:int, c:int, this:Ref);
requires packedCollegeFacilitiesFew[this];
ensures (collegeNumber[this] == c) && (num <= 4 * c);

procedure ConstructCollege(number:int, this:Ref) 
modifies collegeNumber, endowment;
ensures packedCollegeFields[this] &&
	(fracCollegeFields[this] == 1.0);
// TODO need to put in statements about the parameters.
// ensures this#1.0 CollegeFields()[number, (number*1000)-5]
{
	collegeNumber[this] := number;
	endowment[this] := (number *1000) - 5;
}

procedure getCollegeNumber(this:Ref) returns (r:int)
ensures packedCollegeNumberField[this] &&
	(fracCollegeNumberField[this] == 1.0);
// TODO add statement about value of parameter 
// ensures this#1.0 CollegeNumberField()[result]
{
	r := collegeNumber[this];
}

// the method that calculates the extrinsic state
procedure getNumberFacilities(int campusNumber) returns (r:Ref)
requires packedCollegeNumberField[this] && 
	(fracCollegeNumberField[this] == 1.0);
//TODO have to say what are the current values of the parameters
// requires this#1 CollegeNumberField(this.collegeNumber)
ensures packedMultipleOf[r] &&
	(fracMultipleOf[r] == 1.0);
//ensures result#1 MultipleOf(this.collegeNumber)
{
	call ConstructIntCell(collegeNumber[this] * campusNumber, r);
}

procedure checkFewFacilities(num:int) returns (b:bool)
requires packedCollegeFacilitiesFew[this] &&
	(fracCollegeFacilitiesFew[this] == 1.0);
//requires this#1 collegeFacilitiesFew(num)
ensures packedCollegeFacilitiesFew[this] &&
	(fracCollegeFacilitiesFew[this] == 1.0);
//ensures this#1 collegeFacilitiesFew(num)
{
	r := (num <= 4 * collegeNumber[this]);
}

procedure checkManyFacilities(int num) returns (b:bool)
requires packedCollegeFacilitiesMany[this] &&
	(fracCollegeFacilitiesMany[this] == 1.0);
//requires this#1 collegeFacilitiesMany(num)
ensures packedCollegeFacilitiesMany[this] &&
	(fracCollegeFacilitiesMany[this] == 1.0);
//ensures this#1 collegeFacilitiesMany(num)
{
	r := (num >= 10 * collegeNumber[this]);
}
