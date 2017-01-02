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
requires (college[this] == c) && (campusNumber[this] == camp);

procedure UnpackStudentApplicationFields(c:Ref, camp:int, this:Ref);
requires packedStudentApplicationFields[this];
ensures (college[this] == c) && (campusNumber[this] == camp);

procedure PackStudentAppFacilitiesMany(col:Ref, c:int, f:Ref, this:Ref);
requires packedStudentAppFacilitiesMany[this] == false;
requires (college[this] == col) && (campusNumber[this] == c) &&
	(facilities[this] == f) && 
	packedCollegeFacilitiesMany[col] &&
	(fracCollegeFacilitiesMany[col] > 0.0);
//TODO add ensures about params in this object proposition

procedure UnpackStudentAppFacilitiesMany(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this];
ensures (college[this] == col) && (campusNumber[this] == c) &&
	packedCollegeFacilitiesMany[col] &&
	(fracCollegeFacilitiesMany[col] > 0.0);

procedure PackStudentAppFacilitiesFew(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this] == false;
requires (college[this] == col) && (campusNumber[this] == c) &&
	packedCollegeFacilitiesFew[col] &&
	(fracCollegeFacilitiesFew[col] > 0.0);
//TODO add ensures about params in this object proposition

procedure UnpackStudentAppFacilitiesFew(col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this];
ensures (college[this] == col) && (campusNumber[this] == c) &&
	packedCollegeFacilitiesFew[col] &&
	(fracCollegeFacilitiesFew[col] > 0.0);

procedure ConstructStudentApplication(col:Ref, campusNum:int, this:Ref) 
modifies college, facilities, campusNumber;
ensures packedStudentApplicationFields[this] &&
	(fracStudentApplicationFields[this] == 1.0)
{
		college[this] := col;
		call facilities[this] := getNumberFacilities(campusNum, college[this]);
		campusNumber[this] := campusNum;	
}
	
procedure changeApplicationFew(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities;
requires packedStudentAppFacilitiesFew[this] &&
	(fracStudentAppFacilitiesFew[this] == 1.0);
ensures packedStudentAppFacilitiesFew[this] &&
	(fracStudentAppFacilitiesFew[this] == 1.0);
{
	campusNumber[this] := modulo(newCampusNumber, 4);
	call facilities[this] := getNumberFacilities(campusNumber[this], college[this]);
}

procedure changeApplicationMany(newCampusNumber:int, this:Ref)
modifies campusNumber, facilities;
requires packedStudentAppFacilitiesMany[this] &&
	(fracStudentAppFacilitiesMany[this] == 1.0);
ensures packedStudentAppFacilitiesMany[this] &&
	(fracStudentAppFacilitiesMany[this] == 1.0);
{
	campusNumber[this] := newCampusNumber * 10 + 1;
	call facilities[this] := getNumberFacilities(campusNumber[this], college[this]);
}


procedure checkFacilitiesFew(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesFew[this] &&
	(fracStudentAppFacilitiesFew[this] == 1.0);
ensures packedStudentAppFacilitiesFew[this] &&
	(fracStudentAppFacilitiesFew[this] == 1.0);
{        
	var temp:bool;
	call temp := getValueInt(facilities[this]);
	b := (temp <= 4 * campusNumber[this]);
}

procedure checkFacilitiesMany(this:Ref) returns (b:bool)
requires packedStudentAppFacilitiesMany[this] &&
	(fracStudentAppFacilitiesMany[this] == 1.0);
ensures packedStudentAppFacilitiesMany[this] &&
	(fracStudentAppFacilitiesMany[this] == 1.0);
{       
	var temp:bool;
	call temp := getValueInt(facilities[this]);
	b := (temp >= 10 * campusNumber[this]);
}

