var collegeNumber :[Ref]int;
var numberBuildings : [Ref]int;

var packedCollegeNumberField : [Ref]bool;
var fracCollegeNumberField : [Ref]real;

var packedNumberBuildingsField : [Ref]bool;
var fracNumberBuildingsField : [Ref]real;

var packedCollegeBuildingsMany : [Ref]bool;
var fracCollegeBuildingsMany : [Ref]real;

var packedCollegeBuildingsFew : [Ref]bool;
var fracCollegeBuildingsFew : [Ref]real;

procedure PackCollegeNumberField(c: int, this:Ref);
requires (packedCollegeNumberField[this]==false) &&
 	(collegeNumber[this] == c); 

procedure UnpackCollegeNumberField(c: int, this:Ref);
requires packedCollegeNumberField[this];
ensures	(collegeNumber[this] == c);


predicate collegeBuildingsMany() = 
	exists c:int, n:int ::
		(this.collegeNumber -> c) && (this.numberBuildings -> n) && 
		(n == 10 * c)
		
predicate collegeBuildingsFew() = exists c:int, n:int ::
	(this.collegeNumber -> c) && (this.numberBuildings -> n) && (n == 4 * c) 


void setCollege(int number, int multNumber) 
requires
ensures
{
	this.collegeNumber = number;
	this.numberBuildings = this.collegeNumber * multNumber;
}

int getCollegeNumber() 
requires
ensures
{
	return this.collegeNumber;
}

IntCell getNumberFacilities(int campusNumber) 
requires this#1 CollegeNumberField(this.collegeNumber)
ensures result#1 MultipleOf(this.collegeNumber)
{
return new IntCell(campusNumber * this.collegeNumber);
}

boolean checkFewBuildings() 
requires this#1 collegeBuildingsFew()
ensures this#1 collegeBuildingsFew()
{
return (this.numberBuildings == 4 * this.collegeNumber);
}

boolean checkManyBuildings() 
requires this#1 collegeBuildingsMany()
ensures this#1 collegeBuildingsMany()
{
return (this.numberBuildings == 10 * this.collegeNumber);
}

