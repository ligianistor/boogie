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
requires fa >= 10 * collegeNumber[col];

procedure UnpackStudentAppFacilitiesMany(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesMany[this];
requires fracStudentAppFacilitiesMany[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesMany[col];
ensures	(fracCollegeFacilitiesMany[col] > 0.0);
ensures fa >= 10 * collegeNumber[col];

procedure PackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this] == false;
requires (college[this] == col);
requires (campusNumber[this] == c);
requires packedCollegeFacilitiesFew[col];
requires (fracCollegeFacilitiesFew[col] > 0.0);
requires fa <= 4 * collegeNumber[col];

procedure UnpackStudentAppFacilitiesFew(fa:int, col:Ref, c:int, this:Ref);
requires packedStudentAppFacilitiesFew[this];
requires fracStudentAppFacilitiesFew[this] > 0.0;
ensures (college[this] == col);
ensures	(campusNumber[this] == c);
ensures	packedCollegeFacilitiesFew[col];
ensures	(fracCollegeFacilitiesFew[col] > 0.0);
ensures fa <= 4 * collegeNumber[col];

procedure ConstructStudentApplication(col:Ref, campusNum:int, this:Ref) 
modifies college, facilities, campusNumber, fracMultipleOf, packedMultipleOf, divider, value,
        packedCollegeFacilitiesFew, packedCollegeFacilitiesMany
        , fracCollegeFacilitiesFew, fracCollegeFacilitiesMany,
        packedCollegeNumberField;
  requires campusNum > 0;
  requires packedCollegeNumberField[col]==false;
  requires fracCollegeNumberField[col] > 0.0;
requires collegeNumber[col] > 0;
  ensures (college[this] == col);
  ensures (campusNumber[this] == campusNum);
  ensures ( (campusNum <= 4) && (campusNum > 0)  )==> ( packedCollegeFacilitiesFew[col] && 
	(fracCollegeFacilitiesFew[col] > 0.0)  && (facilities[this] == collegeNumber[col] * campusNum) );
  ensures (campusNum >= 10) ==> ( packedCollegeFacilitiesMany[col] &&
	(fracCollegeFacilitiesMany[col] > 0.0)  && (facilities[this] == collegeNumber[col] * campusNum) );

{
    var temp : int;
		college[this] := col;
		call temp := getNumberFacilities(campusNum, collegeNumber[college[this]], college[this]);
    facilities[this] := temp;// !!!Here I need to add in the Java program what is the
    // new predicate that has to hold about col, because only now I have all the information
    // to know which predicate holds.
    // I have a fraction to col since it is given as input.
		campusNumber[this] := campusNum;	
    if (0 < campusNum  && campusNum <= 4) {
      packedCollegeFacilitiesFew[college[this]] := packedCollegeNumberField[college[this]];
      fracCollegeFacilitiesFew[college[this]] :=fracCollegeNumberField[college[this]];
      call PackCollegeFacilitiesFew(facilities[this], collegeNumber[college[this]], college[this]);
      packedCollegeFacilitiesFew[college[this]] := true;
      
    } else if (campusNum >= 10) {
      packedCollegeFacilitiesMany[college[this]] := packedCollegeNumberField[college[this]];
     fracCollegeFacilitiesMany[college[this]] := fracCollegeNumberField[college[this]];
      call PackCollegeFacilitiesMany(facilities[this] ,collegeNumber[college[this]], college[this]);
      packedCollegeFacilitiesMany[college[this]] := true;
     
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
  call UnpackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
  packedStudentAppFacilitiesFew[this] := false;
	campusNumber[this] := modulo(newCampusNumber, 4) + 1;
    
    //transfer
    packedCollegeNumberField[college[this]] := packedCollegeFacilitiesFew[college[this]];
    fracCollegeNumberField[college[this]] := fracCollegeFacilitiesFew[college[this]];

    call UnpackCollegeNumberField(collegeNumber[college[this]], college[this]);
    packedCollegeNumberField[college[this]] := false;
	call temp := getNumberFacilities(campusNumber[this], collegeNumber[college[this]], college[this]);
  facilities[this] := temp;
  call PackStudentAppFacilitiesFew(facilities[this], college[this], campusNumber[this], this);
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
    call UnpackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
    packedStudentAppFacilitiesMany[this] := false;
	  campusNumber[this] := newCampusNumber * 10 + 1;
    
    //transfer
    packedCollegeNumberField[college[this]] := packedCollegeFacilitiesMany[college[this]];
    fracCollegeNumberField[college[this]] := fracCollegeFacilitiesMany[college[this]];

    call UnpackCollegeNumberField(collegeNumber[college[this]], college[this]);
    packedCollegeNumberField[college[this]] := false;
	  call temp := getNumberFacilities(campusNumber[this],collegeNumber[college[this]], college[this]);
  	facilities[this] := temp;
    call PackStudentAppFacilitiesMany(facilities[this], college[this], campusNumber[this], this);
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


