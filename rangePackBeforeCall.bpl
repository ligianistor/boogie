type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null : Ref;
const unique RangeP : PredicateTypes;

var val : [Ref]int;
var next : [Ref]Ref;

var frac : FractionType;
var packed : PackedType;

var xRangePred : [Ref] int;
var yRangePred : [Ref] int;

procedure ConstructRange0(this: Ref, v: int, n: Ref);
	ensures (val[this] == v) && 
		(next[this] == n) && 
		(packed[this, RangeP]) && 
		(frac[this, RangeP] >= 100);

procedure ConstructRange(this: Ref, v: int, n: Ref);
	ensures (val[this] == v) && 
		(next[this] == n);

procedure PackRange(this:Ref, x:int, y:int);
	requires (this != null);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ( (next[this] == null) || 
		 	(packed[next[this], RangeP] &&
			(frac[next[this], RangeP] >= 1) &&
			(xRangePred[next[this]] == x) && 
			(yRangePred[next[this]] == y))
		 );
	ensures (xRangePred[this]==x) && (yRangePred[this]==y);

procedure UnpackRange(this:Ref, x:int, y:int);
	requires packed[this, RangeP];
	requires (xRangePred[this] == x);
	requires (yRangePred[this] == y);
	requires (frac[this, RangeP] >= 1);
	ensures (this != null) && 
		 (val[this] >= x) &&
		 (val[this] <= y) &&
		 ( (next[this] == null) || 
		 	(packed[next[this], RangeP] &&
			(frac[next[this], RangeP] >= 1) &&
			(xRangePred[next[this]] == x) && 
			(yRangePred[next[this]] == y))
		 );
  
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
	modifies val, packed, frac;
	requires this!=null;
	requires x >= 0;
	requires frac[this, RangeP] >= 1;
	requires xRangePred[this] == 0; 
	requires yRangePred[this] == 10;
	requires packed[this, RangeP];
	ensures packed[this, RangeP];
	ensures xRangePred[this] == 0; 
	ensures yRangePred[this] == 10;
	ensures frac[this, RangeP] >= 1;
	ensures (forall y:Ref :: (packed[y, RangeP] == old(packed[y, RangeP])) );
	ensures (forall y:Ref :: (frac[y, RangeP] == old(frac[y, RangeP])) );
{
	//there are no cycles condition
	assume (forall link:Ref :: (this != next[link]));

	call UnpackRange(this, 0, 10);
	packed[this, RangeP] := false;

	val[this] := modulo((val[this]+x),11);
  
  	call PackRange(this, 0, 10);
	packed[this,RangeP] := true;
	
	if (next[this] != null )
	{ 
		call addModulo11(next[this], x);
		frac[next[this], RangeP] := frac[next[this], RangeP] - 1;
		frac[next[this], RangeP] := frac[next[this], RangeP] + 1;
	}
}
