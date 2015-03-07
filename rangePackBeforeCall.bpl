//The name of this class is Link.
type Ref;
type FractionRangeType = [int, int, Ref] real;
type PackedRangeType = [int, int, Ref] bool;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : FractionRangeType;
var packedRange : PackedRangeType;


procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

// We assume that packedRange[x,y, next[this]] holds
// because it is the invariant
// so we do not need to add it in the requires of PackRange.
// How do we know that this is the invariant for next[this]?
// We do not need to have packedRange[x,y,next[this]]
// in the requires.
// When you unpack something, you assume that all the object propositions inside it are packed. 
// That's why we need the ensures packedRange[] there. It is like an assume.
// When you pack something, you need just a fraction, so you don't actually need the requires packedRange[].
procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (fracRange[x,y,next[this]] > 0.0) );

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[x,y,this];
	requires (fracRange[x,y,this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (
		  (fracRange[x,y,next[this]] > 0.0) )
		 );

procedure PackUniRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (fracRange[x,y,next[this]] == 1.0) );

procedure UnpackUniRange(x:int, y:int, this:Ref);
	requires packedRange[x,y,this];
	requires (fracRange[x,y,this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (
		  (fracRange[x,y,next[this]] == 1.0) )
		 );
  
procedure addModulo11(x:int, this: Ref);
	modifies val, packedRange, fracRange;
	requires x >= 0;
	requires fracRange[0,10,this] > 0.0;
  	requires (forall y:Ref :: (packedRange[0,10,y] == true));
	ensures packedRange[0,10,this];
	ensures fracRange[0,10,this] > 0.0;
	//This says that Range is an invariant of all the objects in this method.
	ensures (forall y:Ref :: (packedRange[0,10,y] == old(packedRange[0,10,y])) );
	ensures (forall y:Ref :: (fracRange[0,10,y] == old(fracRange[0,10,y])) );
{
	call UnpackRange(0, 10, this);
	packedRange[0,10,this] := false;
	fracRange[0,10,next[this]] := fracRange[0,10,next[this]] * 2.0;

	val[this] := modulo((val[this]+x),11);
  
  	call PackRange(0, 10, this);
	packedRange[0,10,this] := true;
	fracRange[0,10,next[this]] := fracRange[0,10,next[this]] / 2.0;
	
	if (next[this] != null )
	{ 
    		call addModulo11(x, next[this]);
		fracRange[0,10,next[this]] := fracRange[0,10,next[this]] * 2.0;
		fracRange[0,10,next[this]] := fracRange[0,10,next[this]] / 2.0;
	}
}

    void add(int z)
    int x, int y: //SpecExpression with list of declaration
    requires x < y && (this#1 UniRange(x,y))
    ensures (this#1 UniRange(x+z,y+z))
    {
    	unpack(this#1 UniRange(x,y));
    	this.val = this.val + z;
    	pack(this#1 UniRange(x+z,y+z));
    	if (this.next != null) {
    		this.next.add(z);
    	}
    }

procedure add(z:int, x:int, y:int, this: Ref);
	modifies val, packedRange, fracRange;
	requires x < y;
	requires fracUniRange[x,y,this] > 0.0;
  	requires (forall x0:Ref :: (packedUniRange[x,y,x0] == true));
	ensures packedUniRange[x,y,this];
	ensures fracUniRange[x,y,this] > 0.0;
	//This says that Range is an invariant of all the objects in this method.
	ensures (forall x0:Ref :: (packedUniRange[x,y,x0] == old(packedUniRange[x,y,x0])) );
	ensures (forall x0:Ref :: (fracUniRange[x,y,x0] == old(fracUniRange[x,y,x0])) );
{
	call UnpackUniRange(x, y, this);
	packedUniRange[x,y,this] := false;
	fracUniRange[x,y,next[this]] := fracRange[x,y,next[this]] * 2.0;

	val[this] := modulo((val[this]+x),11);
  
  	call PackUniRange(0, 10, this);
	packedRange[0,10,this] := true;
	fracRange[0,10,next[this]] := fracRange[0,10,next[this]] / 2.0;
	
	if (next[this] != null )
	{ 
    		call add(z, x, y, next[this]);
		fracUniRange[0,10,next[this]] := fracUniRange[0,10,next[this]] * 2.0;
		fracUniRange[0,10,next[this]] := fracUniRange[0,10,next[this]] / 2.0;
	}
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
   	requires (forall y:Ref :: (packedRange[0,10,y] == true));
{
	var l1 : Ref;
	var l2 : Ref;
	var l3 : Ref;
	//Need to state that l1 satisfies the Range predicate.
	//TODO need to add fraction manipulation
	call ConstructLink(0, 10, 3, null, l1);
	packedRange[0,10,l1] := true;
	fracRange[0,10,l1] := 1.0;

	call ConstructLink(0, 10, 4, l1, l2);
	fracRange[0,10,l1] := fracRange[0,10,l1] / 2.0;
	packedRange[0,10,l2] := true;
	fracRange[0,10,l2] := 1.0;

	call ConstructLink(0, 10, 5, l2, l3);
	fracRange[0,10,l2] := fracRange[0,10,l2] / 2.0;
	packedRange[0,10,l3] := true;
	fracRange[0,10,l3] := 1.0;

	call addModulo11(20, l3); 
}




