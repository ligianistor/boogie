//The name of this class is Link.
type Ref;
type FractionRangeType = [int, int, Ref] real;
type PackedRangeType = [int, int, Ref] bool;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : FractionRangeType;
var packedRange : PackedRangeType;


procedure ConstructLinkRange(x: int, y:int, v: int, n: Ref, this: Ref);
	ensures (val[this] == v) && 
		(next[this] == n) && 
		(packedRange[x,y,this]) && 
		(fracRange[x,y,this] == 1.0);

procedure ConstructLink(v: int, n: Ref, this: Ref);
	ensures (val[this] == v) && 
		(next[this] == n);


// We assume that packedRange[x,y, next[this]] holds
// because it is the invariant
// so we do not need to add it in the requires of PackRange.
// How do we know that this is the invariant for next[this]?
procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (packedRange[x,y,next[this]] &&
		  (fracRange[x,y,next[this]] > 0.0) )
		   );

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[x,y,this];
	requires (fracRange[x,y,this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (packedRange[x,y,next[this]] &&
		  (fracRange[x,y,next[this]] > 0.0) )
		 );
  
procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange;
	requires x >= 0;
	requires fracRange[0,10,this] > 0.0;

	requires packedRange[0,10,this];
	ensures packedRange[0,10,this];
	ensures fracRange[0,10,this] > 0.0;
	ensures (forall y:Ref :: (packedRange[0,10,y] == old(packedRange[0,10,y])) );
	//maybe this should be
	//ensures (forall y:Ref :: (fracRange[y] > 0.0) );
	ensures (forall y:Ref :: (fracRange[0,10,y] == old(fracRange[0,10,y])) );
{
	//There are no cycles condition below.
	//But even if there is a cycle, the verification should work by default.
	//assume (forall link:Ref :: (this != next[link]));

	call UnpackRange(0, 10, this);
	packedRange[0,10,this] := false;

	val[this] := modulo((val[this]+x),11);
  
	//fracRange[0,10,next[this]] := fracRange[0,10,next[this]] * 2.0;

  	call PackRange(0, 10, this);
	packedRange[0,10,this] := true;
	
	if (next[this] != null )
	{ 
		call addModulo11(x, next[this]);
		fracRange[0,10,next[this]] := fracRange[0,10,next[this]] * 2.0;
		fracRange[0,10,next[this]] := fracRange[0,10,next[this]] / 2.0;
	}
	// I don't know why this is here.
	//fracRange[0,10,next[this]] := fracRange[0,10,next[this]] / 2.0;
}

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



