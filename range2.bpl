type Ref;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : [Ref] real;
var packedRange : [Ref] bool;
var fracUniRange : [Ref] real;
var packedUniRange : [Ref] bool;
var paramxRange : [Ref] int;
var paramyRange : [Ref] int;
var paramxUniRange : [Ref] int;
var paramyUniRange : [Ref] int;


procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (fracRange[next[this]] > 0.0)
	 );

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[this];
	requires (fracRange[this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (fracRange[next[this]] > 0.0) 
		 );

procedure PackUniRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  (fracUniRange[next[this]] == 1.0));

procedure UnpackUniRange(x:int, y:int, this:Ref);
	requires packedUniRange[this];
	requires (fracUniRange[this] > 0.0);
	requires (paramxUniRange[this] == x);
	requires (paramyUniRange[this] == y);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  (fracUniRange[next[this]] == 1.0) 
		 );
//We either don't allow predicates that are that variable
//or we accept that we can say that we pack to a certain predicate,
//but we do not know the exact parameters
//and when the programmer write unpack(params)
//we assume that those parameters are right.
procedure add(z:int, x:int, y:int, this: Ref)
	modifies val, packedUniRange, fracUniRange, paramxUniRange, paramyUniRange;
	requires x < y;
	requires fracUniRange[this] == 1.0;
  	requires (forall x0:Ref :: packedUniRange[x0]);
	requires paramxUniRange[this] == x;
	requires paramyUniRange[this] == y;
	ensures packedUniRange[this];
	ensures paramxUniRange[this] == x+z;
	ensures paramyUniRange[this] == y+z;
	ensures fracUniRange[this] == 1.0;
	ensures (forall x0:Ref :: packedUniRange[x0]);
{
	call UnpackUniRange(x, y, this);
	packedUniRange[this] := false;

	val[this] := val[this]+z;

  	fracUniRange[next[this]] := 1.0;
  	call PackUniRange(x+z, y+z, this);
	packedUniRange[this] := true;
	fracUniRange[next[this]] :=  1.0;
	paramxUniRange[this] := x+z;
	paramyUniRange[this] := y+z;
	
	if (next[this] != null )
	{ 
    		call add(z, x, y, next[this]);
	}
}
  
procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange, paramxRange, paramyRange;
	requires x >= 0;
	requires fracRange[this] > 0.0;
	requires paramxRange[this] == 0;
	requires paramyRange[this] == 10;
  	requires (forall y:Ref :: (packedRange[y] == true));
	ensures packedRange[this];
	ensures paramxRange[this] == 0;
	ensures paramyRange[this] == 10;
	ensures fracRange[this] > 0.0;
	ensures (forall y:Ref :: (packedRange[y] == old(packedRange[y])) );
	ensures (forall y:Ref :: (fracRange[y] == old(fracRange[y])) );
{
	call UnpackRange(0, 10, this);
	packedRange[this] := false;
	fracRange[next[this]] := fracRange[next[this]] * 2.0;

	val[this] := modulo((val[this]+x),11);
  
  	call PackRange(0, 10, this);
	packedRange[this] := true;
	paramxRange[this] := 0;
	paramyRange[this] := 10;
	fracRange[next[this]] := fracRange[next[this]] / 2.0;
	paramxRange[this] := 0;
	
	if (next[this] != null )
	{ 
    
		call addModulo11(x, next[this]);
		fracRange[next[this]] := fracRange[next[this]] * 2.0;
		fracRange[next[this]] := fracRange[next[this]] / 2.0;
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
	modifies val, packedRange, fracRange, paramxRange, paramyRange;
   requires (forall y:Ref :: (packedRange[y] == true));
{
	var l1 : Ref;
	var l2 : Ref;
	var l3 : Ref;
	call ConstructLink(0, 10, 3, null, l1);
	packedRange[l1] := true;
	fracRange[l1] := 1.0;
	paramxRange[l1] := 0;
	paramyRange[l1] := 10;


	call ConstructLink(0, 10, 4, l1, l2);
	fracRange[l1] := fracRange[l1] / 2.0;
	packedRange[l2] := true;
	fracRange[l2] := 1.0;
	paramxRange[l2] := 0;
	paramyRange[l2] := 10;

	call ConstructLink(0, 10, 5, l2, l3);
	fracRange[l2] := fracRange[l2] / 2.0;
	packedRange[l3] := true;
	fracRange[l3] := 1.0;
	paramxRange[l3] := 0;
	paramyRange[l3] := 10;

	call addModulo11(20, l3); 
}





