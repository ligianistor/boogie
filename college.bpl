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

