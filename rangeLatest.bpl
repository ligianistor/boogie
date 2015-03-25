type Ref;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : [int, int, Ref] real;
var packedRange : [int, int, Ref] bool;
var fracUniRange : [int, int, Ref] real;
var packedUniRange : [int, int, Ref] bool;


procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

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

procedure add(z:int, x:int, y:int, this: Ref)
	modifies val, packedUniRange, fracUniRange;
	requires x < y;
	requires fracUniRange[x,y,this] == 1.0;
  requires (forall x0:Ref :: (packedUniRange[x,y,x0] == true));
	ensures packedUniRange[x+z,y+z,this];
	ensures fracUniRange[x+z,y+z,this] == 1.0;
	ensures (forall x0:Ref :: packedUniRange[x+z,y+z,x0]);
{
	call UnpackUniRange(x, y, this);
	packedUniRange[x,y,this] := false;
	fracUniRange[x,y,next[this]] := fracUniRange[x,y,next[this]] - 1.0;

	val[this] := val[this]+z;
  
  	call PackUniRange(x+z, y+z, this);
	packedUniRange[x+z,y+z,this] := true;
	fracUniRange[x+z,y+z,next[this]] := fracUniRange[x+z,y+z,next[this]] + 1.0;
	
	if (next[this] != null )
	{ 
    		call add(z, x, y, next[this]);
	}
}
  
procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange;
	requires x >= 0;
	requires fracRange[0,10,this] > 0.0;
  requires (forall y:Ref :: (packedRange[0,10,y] == true));
	ensures packedRange[0,10,this];
	ensures fracRange[0,10,this] > 0.0;
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





