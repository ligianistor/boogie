//The name of this class is Link.
type Ref;
type PredicateTypes;
type FractionType = [Ref] real;
type PackedType = [Ref] bool;

const null : Ref;
const unique RangeP : PredicateTypes;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : FractionType;
var packedRange : PackedType;

var xRangePred : [Ref] int;
var yRangePred : [Ref] int;

procedure ConstructLinkRange(rangeMin: int, rangeMax:int, v: int, n: Ref, this: Ref);
	ensures (val[this] == v) && 
		(next[this] == n) && 
		(xRangePred[this] == rangeMin) &&
		(yRangePred[this] == rangeMax) &&
		(packedRange[this]) && 
		(fracRange[this] == 1.0);

procedure ConstructLink(v: int, n: Ref, this: Ref);
	ensures (val[this] == v) && 
		(next[this] == n);

procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (fracRange[next[this]] > 0.0) 
		   );
	ensures (xRangePred[this]==x) && (yRangePred[this]==y);

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[this];
	requires (xRangePred[this] == x);
	requires (yRangePred[this] == y);
	requires (fracRange[this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (packedRange[next[this]] &&
		  (fracRange[next[this]] > 0.0) &&
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

procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange;
	requires x >= 0;
	requires fracRange[this] > 0.0;
	requires xRangePred[this] == 0; 
	requires yRangePred[this] == 10;
	requires packedRange[this];
	ensures packedRange[this];
	ensures xRangePred[this] == 0; 
	ensures yRangePred[this] == 10;
	ensures fracRange[this] > 0.0;
	ensures (forall y:Ref :: (packedRange[y] == old(packedRange[y])) );
	//maybe this should be
	//ensures (forall y:Ref :: (fracRange[y] > 0.0) );
	ensures (forall y:Ref :: (fracRange[y] == old(fracRange[y])) );
{
	//there are no cycles condition
	//assume (forall link:Ref :: (this != next[link]));

	call UnpackRange(0, 10, this);
	packedRange[this] := false;

	val[this] := modulo((val[this]+x),11);
  
	fracRange[next[this]] := fracRange[next[this]] * 2.0;

  	call PackRange(0, 10, this);
	packedRange[this] := true;
	
	if (next[this] != null )
	{ 
		call addModulo11(x, next[this]);
		fracRange[next[this]] := fracRange[next[this]] * 2.0;
		fracRange[next[this]] := fracRange[next[this]] / 2.0;
	}
	fracRange[next[this]] := fracRange[next[this]] / 2.0;
}


procedure main()
	modifies val, packedRange, fracRange;
{
	var l1 : Ref;
	var l2 : Ref;
	var l3 : Ref;
	//Need to state that l1 satisfies the Range predicate.
	//TODO need to add fraction manipulation
	call ConstructLinkRange(0, 10, 3, null, l1);

	call ConstructLinkRange(0, 10, 4, l1, l2);

	call ConstructLinkRange(0, 10, 5, l2, l3);

	call addModulo11(20, l3); 
}



