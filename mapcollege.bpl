type MapIntCollege = [int] Ref;

// Each ApplicationWebsite will have its own map of college.
var mapOfColleges : [Ref]MapIntCollege; 

var maxSize : [Ref]int;
var size : [Ref]int;

// the type of packed and frac is different here because 
// we are dealing with maps and they have an extra index , the key, 
// that we need in order to get to the value.
var packedIsEntryNull : [Ref, int]bool;
var fracIsEntryNull : [Ref, int]real;

procedure PackIsEntryNull(key1 : int, m:MapIntCollege, this:Ref);
requires  (packedIsEntryNull[this] == false);
requires (mapOfColleges[this] == m) && (m[key1] == null);

procedure ConstructMapCollege(m: MapIntCollege, max:int, s:int, this: Ref);
	ensures (mapOfColleges[this] == m) && (maxSize[this] == max) 
		&& (size[this] == s)

procedure makeMapNull(i : int, this:Ref)
ensures (forall j:int :: (j<=i) => packedIsEntryNull[this, j])
{
if (i==0) {
	mapOfColleges[this][i] := null;	
} else {
	call makeMapNull(i-1, this);
}
}

procedure containsKey(key1: int) returns (b:bool) {
	b := true;
	if (mapOfColleges[this][key1] == null) {
		b := false;	
	} 
}
	
procedure put(key1 : int, college1: Ref, this:Ref) {
	mapOfColleges[this][key1] := college1;	
}
	
procedure get(key1:int) returns (c:Ref)

{
	c := 	mapOfColleges[this][key1];
}
	
College lookup(int collegeNumber, int multNumber) {
	if (!this.containsKey(collegeNumber)) {
		this.put(collegeNumber, new College(collegeNumber, multNumber));
	}
		return this.get(collegeNumber);
}



