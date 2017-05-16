type Ref;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : [Ref] real;
var packedRange : [Ref] bool;
var fracUniRange : [Ref] real;
var packedUniRange : [Ref] bool;
var paramRangeX : [Ref] int;
var paramRangeY : [Ref] int;
var paramUniRangeX : [Ref] int;
var paramUniRangeY : [Ref] int;

procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
  	requires (next[this] != this);
	requires ((next[this] == null) ||
		  ((fracRange[next[this]] > 0.0) && (paramRangeX[next[this]]==x) && (paramRangeY[next[this]]==y))
	 );

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[this];
	requires (fracRange[this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		 ( (fracRange[next[this]] > 0.0) && (paramRangeX[next[this]]==x) && (paramRangeY[next[this]]==y))
		 );
  ensures (next[this] != this);

procedure PackUniRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		(
		(fracUniRange[next[this]] == 1.0) &&
    		packedUniRange[next[this]] &&
		(paramUniRangeX[next[this]] == x) &&
		(paramUniRangeY[next[this]] == y)
		)
);

procedure UnpackUniRange(x:int, y:int, this:Ref);
	requires packedUniRange[this];
	requires (fracUniRange[this] > 0.0);
	requires (paramUniRangeX[this] == x);
	requires (paramUniRangeY[this] == y);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		((fracUniRange[next[this]] == 1.0) &&
         	packedUniRange[next[this]] &&
		(paramUniRangeX[next[this]] == x) &&
		(paramUniRangeY[next[this]] == y)
) 
		 );
    ensures (next[this] != this);	

procedure add(z:int, x:int, y:int, this: Ref)
	modifies val, packedUniRange, fracUniRange, 
		paramUniRangeX, paramUniRangeY;
	requires x < y;
	requires fracUniRange[this] == 1.0;
  	requires packedUniRange[this];
	requires paramUniRangeX[this] == x;
	requires paramUniRangeY[this] == y;
	ensures packedUniRange[this];
	ensures paramUniRangeX[this] == x+z;
	ensures paramUniRangeY[this] == y+z;
	ensures packedUniRange[this];
  	ensures fracUniRange[this] == 1.0;
  	ensures (forall y1:Ref :: (packedUniRange[y1] == old(packedUniRange[y1])) );
	ensures (forall y1:Ref :: (fracUniRange[y1] == old(fracUniRange[y1])) ); 
	free ensures (forall y1:Ref :: ((y1!=this) && (fracUniRange[y1] == 1.0))
    ==> (val[y1] == old(val[y1])));

{
	call UnpackUniRange(x, y, this);

	packedUniRange[this] := false;
	val[this] := val[this]+z;


	if (next[this] != null )
	{  
    call add(z, x, y, next[this]);   
	}

  	call PackUniRange(x+z, y+z, this);
	packedUniRange[this] := true;
	fracUniRange[this] :=  1.0;
	paramUniRangeX[this] := x+z;
	paramUniRangeY[this] := y+z;
}

procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange, paramRangeX, paramRangeY;
	requires x >= 0;
	requires fracRange[this] > 0.0;
	requires paramRangeX[this] == 0;
	requires paramRangeY[this] == 10;
  requires (forall y:Ref :: packedRange[y]);
	requires (forall y:Ref :: paramRangeX[y] == 0);
	requires (forall y:Ref :: paramRangeY[y] == 10);
	ensures packedRange[this];
	ensures fracRange[this] > 0.0;
	ensures (forall y:Ref :: (packedRange[y] == old(packedRange[y])) );
  ensures (forall y:Ref :: (paramRangeX[y] == old(paramRangeX[y])) );
	ensures (forall y:Ref :: (fracRange[y] == old(fracRange[y])) );
  ensures (forall y:Ref :: (paramRangeX[y] == old(paramRangeX[y])) );
{
	call UnpackRange(0, 10, this);
	packedRange[this] := false;
	fracRange[next[this]] := fracRange[next[this]] * 2.0;

	val[this] := modulo((val[this]+x),11);

	call PackRange(0, 10, this);
	packedRange[this] := true;
	paramRangeX[this] := 0;
	paramRangeY[this] := 10;
	fracRange[next[this]] := fracRange[next[this]] / 2.0;
	
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
	modifies val, packedRange, fracRange, paramRangeX, paramRangeY;
	requires (forall y:Ref :: paramRangeX[y] == 0);
	requires (forall y:Ref :: paramRangeY[y] == 10);
   requires (forall y:Ref :: (packedRange[y] == true));
{
	var l1 : Ref;
	var l2 : Ref;
	var l3 : Ref;
	call ConstructLink(0, 10, 3, null, l1);
	packedRange[l1] := true;
	fracRange[l1] := 1.0;
	paramRangeX[l1] := 0;
	paramRangeY[l1] := 10;


	call ConstructLink(0, 10, 4, l1, l2);
	fracRange[l1] := fracRange[l1] / 2.0;
	packedRange[l2] := true;
	fracRange[l2] := 1.0;
	paramRangeX[l2] := 0;
	paramRangeY[l2] := 10;

	call ConstructLink(0, 10, 5, l2, l3);
	fracRange[l2] := fracRange[l2] / 2.0;
	packedRange[l3] := true;
	fracRange[l3] := 1.0;
	paramRangeX[l3] := 0;
	paramRangeY[l3] := 10;

	call addModulo11(20, l3); 
}





