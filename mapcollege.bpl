type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.
// This field is common with ApplicationWebsite.

var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index, the key, 
// that we need in order to get to the value.
var packedIsEntryNull : [Ref, int]bool;
var fracIsEntryNull : [Ref, int]real;

var packedMapOfCollegesField : [Ref]bool;
var fracMapOfCollegesField : [Ref]real;

procedure PackMapOfCollegesField(m:MapIntCollege, this:Ref);
requires packedMapOfCollegesField[this] == false;
requires mapOfColleges[this] == m;


	predicate MapOfCollegesField() = exists m:map<int, College> :: mapOfColleges -> m
			
	predicate KeyValuePair(int key, College value) = 
			exists m:map<int, College> :: mapOfColleges -> m && (mapOfColleges[key] == value)



procedure PackIsEntryNull(key1 : int, m:MapIntCollege, this:Ref);
requires  (packedIsEntryNull[this] == false);
requires (mapOfColleges[this] == m) && (m[key1] == null);

procedure ConstructMapCollege(m: MapIntCollege, max:int, s:int, this: Ref);
	ensures (mapOfColleges[this] == m) && (maxSize[this] == max) 
		&& (size[this] == s)

procedure makeMapNull(i : int, this:Ref)
modifies mapOfColleges;
ensures (forall j:int :: (j<=i) => packedIsEntryNull[this, j])
{
if (i==0) {
	mapOfColleges[this][i] := null;	
} else {
	call makeMapNull(i-1, this);
}
}

procedure containsKey(key1: int) returns (b:bool)
requires packedMapOfCollegesField[this] &&
	(fracMapOfCollegesField[this] == 1.0);
//requires this#1.0 MapOfCollegesField()
//ensures (b == true) && (exists c:College ==> (this#1.0 KeyValuePair(key1, c))	 ||
//	(b == false) && (this#1.0 KeyValuePair(key1, null)) 
{
	b := true;
	if (mapOfColleges[this][key1] == null) {
		b := false;	
	} 
}
	
procedure put(key1 : int, college1: Ref, this:Ref) 
modifies mapOfColleges;
requires packedMapOfCollegesField[this] &&
	(fracMapOfCollegesField[this] == 1.0);
ensures packedKeyValuePair[this] &&
	(fracKeyValuePair[this] == 1.0);
{
	mapOfColleges[this][key1] := college1;	
}
	
procedure get(key1:int, this:Ref) returns (c:Ref)
requires packedMapOfCollegesField[this] &&
	(fracMapOfCollegesField[this] == 1.0);
ensures packedKeyValuePair[this] &&
	(fracKeyValuePair[this] == 1.0);
// TODO make sure fraction values are right
//requires this#1.0 MapOfCollegesField()
//ensures this#1.0 KeyValuePair(key1, result)
{
	c := mapOfColleges[this][key1];
}
	
procedure lookup(collegeNumber:int, this:Ref) returns (r:Ref)
modifies mapOfColleges;
requires packedMapOfCollegesField[this] &&
	(fracMapOfCollegesField[this] == 1.0);
ensures packedKeyValuePair[this] &&
	(fracKeyValuePair[this] == 1.0);
//ensures this#1.0 KeyValuePair(collegeNumber, result)
{
var temp:bool;
var c:Ref;
call temp := containsKey(collegeNumber, this);
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


