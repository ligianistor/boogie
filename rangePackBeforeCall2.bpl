type Ref;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracRange : [Ref] real;
var paramRangex : [Ref]int;
var paramRangey : [Ref]int; 
var packedRange : [Ref] bool;
var fracUniRange : [Ref] real;
var paramUniRangex : [Ref]int;
var paramUniRangey : [Ref]int; 
var packedUniRange : [Ref] bool;


procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

procedure PackRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		  ((fracRange[next[this]] > 0.0) &&
		(paramRangex[next[this]] == x) &&
		(paramRangey[next[this]] == y)
		)
		);

procedure UnpackRange(x:int, y:int, this:Ref);
	requires packedRange[this];
	requires (paramRangex[this] == x);
	requires (paramRangey[this] == y);
	requires (fracRange[this] > 0.0);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  ((fracRange[next[this]] > 0.0) &&
		(paramRangex[next[this]] == x) &&
		(paramRangey[next[this]] == y)
		)
		 );

procedure PackUniRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		(
		(fracUniRange[next[this]] == 1.0) &&
		(paramUniRangex[next[this]] == x) &&
		(paramUniRangey[next[this]] == y) &&
    		packedUniRange[next[this]] 
		)
);

procedure UnpackUniRange(x:int, y:int, this:Ref);
	requires packedUniRange[this];
	requires (fracUniRange[this] > 0.0);
	requires (paramUniRangex[this] == x);
	requires (paramUniRangey[this] == y);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		((fracUniRange[next[this]] == 1.0) &&
		(paramUniRangex[next[this]] == x) &&
		(paramUniRangey[next[this]] == y) &&
         	packedUniRange[next[this]] ) 
		 );
  
procedure addModulo11(x:int, this: Ref) 
	modifies val, packedRange, fracRange;
	requires x >= 0;
	requires fracRange[this] > 0.0;
	requires paramRangex[this] == 0;
	requires paramRangey[this] == 10;
  	requires (forall y:Ref :: (packedRange[y] == true));
	ensures packedRange[this];
	requires paramRangex[this] == 0;
	requires paramRangey[this] == 10;
	ensures fracRange[this] > 0.0;
	//TODO might need to write about paramRangex and y
	ensures (forall y:Ref :: (packedRange[y] == old(packedRange[y])) );
	ensures (forall y:Ref :: (fracRange[y] == old(fracRange[y])) );
{
	call UnpackRange(0, 10, this);
	packedRange[this] := false;
	fracRange[next[this]] := fracRange[next[this]] * 2.0;

	val[this] := modulo((val[this]+x),11);
  	//TODO need to update the paramRangex and y
  	call PackRange(0, 10, this);
	packedRange[this] := true;
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

procedure add(z:int, x:int, y:int, this: Ref)
	modifies val, packedUniRange, fracUniRange,
		paramUniRangex, paramUniRangey;
	requires x < y;
	requires fracUniRange[this] == 1.0;
  	requires packedUniRange[this];
	requires paramUniRangex[this] == x;
	requires paramUniRangey[this] == y;
	ensures packedUniRange[this];
  	ensures fracUniRange[this] == 1.0;
	requires paramUniRangex[this] == x+z;
	requires paramUniRangey[this] == y+z;
{
	call UnpackUniRange(x, y, this);

	packedUniRange[this] := false;

	val[this] := val[this]+z;
	//TODO update params?

	if (next[this] != null )
	{ 
//The assume is better right before the call because
//there is a rationale for putting it here. 
//Same for the assume right after the call.
	assume (this != next[this]);
    	call add(z, x, y, next[this]);
    	assume (val[this]==old(val[this])+z);
	}
  
  	call PackUniRange(x+z, y+z, this);
	packedUniRange[this] := true;
	fracUniRange[this] :=  1.0;
	paramUniRangex[this] := x+z;
	paramUniRangey[this] := y+z;

}


procedure main()
	modifies val, packedRange, fracRange,
		paramRangex, paramRangey;
//TODO might need to talk about paramRangex and y being 0 and 10
   requires (forall y:Ref :: (packedRange[y] == true));
{
	var l1 : Ref;
	var l2 : Ref;
	var l3 : Ref;
	call ConstructLink(0, 10, 3, null, l1);
	packedRange[l1] := true;
	fracRange[l1] := 1.0;
	paramRangex[l1] := 0;
	paramRangey[l1] := 10;

	call ConstructLink(0, 10, 4, l1, l2);
	fracRange[l1] := fracRange[l1] / 2.0;
	packedRange[l2] := true;
	fracRange[l2] := 1.0;
	paramRangex[l2] := 0;
	paramRangey[l2] := 10;

	call ConstructLink(0, 10, 5, l2, l3);
	fracRange[l2] := fracRange[l2] / 2.0;
	packedRange[l3] := true;
	fracRange[l3] := 1.0;
	paramRangex[l3] := 0;
	paramRangey[l3] := 10;

	call addModulo11(20, l3); 
}





