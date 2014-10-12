//type Ref is intended to represent object references
type Ref;
type PredicateTypes;
type FractionType = [Ref] int;
type PackedType = [Ref, PredicateTypes] bool;

const null:Ref;
const unique RangeP:PredicateTypes;

var val: [Ref]int;
var next: [Ref]Ref;

var fracRangeP: FractionType;
var packed: PackedType;

//global variables that keep track of the parameters of the Range predicate
//that are not values of fields
var xRangePred: [Ref] int;
var yRangePred: [Ref] int;

procedure ConstructRange0(this: Ref, v: int, n: Ref);
	ensures (val[this] == v) && 
		(next[this] == n) && 
		(packed[this, RangeP]) && 
		(fracRangeP[this] >= 100);

//after calling procedures PackRangeNextNull, any kind 
//of Pack procedures, I have to do
//packed[this, rangeP]:=true

//Boogie code needs to be much closer to the Java code. 
//We do not want PackRangeNextNull and PackRangeNextNotNull.
//We only want one PackRange.

//Isn't this != null implied?
procedure PackRange(this:Ref, x:int, y:int);
	requires (this != null) && 
		 (val[this] >= x) &&
		 (val[this] <= y) &&
		 ( (next[this] == null) || 
		 	(packed[next[this], RangeP] &&
			(fracRangeP[next[this]] >= 1) &&
			(xRangePred[next[this]] == x) && 
			(yRangePred[next[this]] == y))
		 );
	ensures (xRangePred[this]==x) && (yRangePred[this]==y);
	//Might need to do the above ensures in an assignment instead?


procedure UnpackRange(this:Ref, x:int, y:int);
	requires packed[this, RangeP] && 
		(xRangePred[this] == x) &&
		(yRangePred[this] == y) &&
		(fracRangeP[this] >= 1);
	ensures (this != null) && 
		 (val[this] >= x) &&
		 (val[this] <= y) &&
		 ( (next[this] == null) || 
		 	(packed[next[this], RangeP] &&
			(fracRangeP[next[this]] >= 1) &&
			(xRangePred[next[this]] == x) && 
			(yRangePred[next[this]] == y))
		 );
 

//modulo is not implemented in Boogie
//so its properties have to be described  
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

procedure addModulo11(this: Ref, x:int) 
modifies val, packed, xRangePred, fracRangeP;
//need to put this in for modulo 
requires this!=null;
//requires x>=0;
//this could be 100 here
requires fracRangeP[this] >= 1;
requires xRangePred[this] == 0; 
requires yRangePred[this] == 10;
requires packed[this, RangeP];
ensures packed[this, RangeP];
ensures xRangePred[this] == 0; 
ensures yRangePred[this] == 10;
ensures fracRangeP[this] >= 1;
{
//We need to be careful about assumes.
//And use them sparingly.
call UnpackRange(this, 0, 10);
 packed[this, RangeP] := false;
 //We need to put this assume in.
 //Maybe we need to state this as a precondition of the method.
//Can state in paper that we learned things like these.
assume this != next[this];
assert (this != null);
assert (val[this] >= 0);
assert (val[this] <= 10); 
assert ( (next[this] == null) || 
		 	(packed[next[this], RangeP] &&
			(fracRangeP[next[this]] >= 1) &&
			(xRangePred[next[this]] == 0) && 
			(yRangePred[next[this]] == 10))
		 ) ;
   

val[this] := modulo((val[this]+x),11);

if (next[this] != null )
  { 
assert next[this] != null;
assert fracRangeP[next[this]] >= 1;
assert xRangePred[next[this]] == 0; 
assert yRangePred[next[this]] == 10;
assert packed[next[this], RangeP];

call addModulo11(next[this], x);
  }

  //val[this] was not modified
  //but Boogie does not know that

call PackRange(this, 0, 10);
packed[this,RangeP]:=true;
  }
