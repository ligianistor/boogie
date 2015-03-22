type Ref;

const null : Ref;

var val : [Ref]int;
var next : [Ref]Ref;

var fracUniRange : [Ref] real;
var packedUniRange : [Ref] bool;
var paramxUniRange : [Ref] int;
var paramyUniRange : [Ref] int;


procedure ConstructLink(x: int, y:int, val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

procedure PackUniRange(x:int, y:int, this:Ref);
	requires (val[this] >= x);
	requires (val[this] <= y);
	requires ((next[this] == null) ||
		(
		(fracUniRange[next[this]] == 1.0) &&
    packedUniRange[next[this]] &&
		(paramxUniRange[next[this]] == x) &&
		(paramyUniRange[next[this]] == y)
		)
);

procedure UnpackUniRange(x:int, y:int, this:Ref);
	requires packedUniRange[this];
	requires (fracUniRange[this] > 0.0);
	requires (paramxUniRange[this] == x);
	requires (paramyUniRange[this] == y);
	ensures  (val[this] >= x) &&
		 (val[this] <= y) &&
		 ((next[this] == null) ||
		  ((fracUniRange[next[this]] == 1.0) &&
         packedUniRange[next[this]] &&
		(paramxUniRange[next[this]] == x) &&
		(paramyUniRange[next[this]] == y)
) 
		 );


procedure add(z:int, x:int, y:int, this: Ref)
	modifies val, packedUniRange, fracUniRange, paramxUniRange, paramyUniRange;
	requires x < y;
	requires fracUniRange[this] == 1.0;
  	requires packedUniRange[this];
	requires paramxUniRange[this] == x;
	requires paramyUniRange[this] == y;
	ensures packedUniRange[this];
	ensures paramxUniRange[this] == x+z;
	ensures paramyUniRange[this] == y+z;
	ensures packedUniRange[this];
  	ensures fracUniRange[this] == 1.0;
{
	call UnpackUniRange(x, y, this);

	packedUniRange[this] := false;

	val[this] := val[this]+z;

    	assume (this != next[this]);
	if (next[this] != null )
	{ 
    	call add(z, x, y, next[this]);
    	assume (val[this]==old(val[this])+z);
	}
  
  	call PackUniRange(x+z, y+z, this);
	packedUniRange[this] := true;
	fracUniRange[this] :=  1.0;
	paramxUniRange[this] := x+z;
	paramyUniRange[this] := y+z;

}

