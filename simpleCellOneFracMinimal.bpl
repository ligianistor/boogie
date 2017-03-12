type Ref;
const null: Ref;

var val: [Ref]int;
var next: [Ref]Ref;
var packedPredNext: [Ref] bool;
var fracPredNext: [Ref] real;
var packedPredVal: [Ref] bool;
var fracPredVal: [Ref] real;
 
procedure ConstructSimpleCell(val1: int, next1: Ref, this: Ref)
	modifies val, next;
	ensures (val[this] == val1) && 
		(next[this] == next1);
	ensures (forall y:Ref :: ( (y!=this) ==> (val[y] == old(val[y]) ) ) );
	ensures (forall y:Ref :: ( (y!=this) ==> (next[y] == old(next[y]) ) ) );
{
	val[this] := val1;
	next[this] := next1;
}

procedure PackPredVal(v:int, this: Ref);
	requires (packedPredVal[this] == false) && 
		(val[this] == v) &&
		(v < 15);

procedure UnpackPredVal(v:int, this: Ref);
	requires packedPredVal[this] &&
		(fracPredVal[this] > 0.0);
	requires (val[this] == v);
	ensures	(v < 15);

procedure PackPredNext(obj:Ref, this: Ref);
	requires (next[this] == obj) &&
		(fracPredVal[obj] >= 0.34) &&
		(packedPredNext[this] == false);

procedure UnpackPredNext(obj:Ref, this: Ref);
	requires packedPredNext[this] &&
		(fracPredNext[this] > 0.0);
	requires (next[this] == obj);
	
procedure changeVal(this: Ref, r: int)
	modifies packedPredVal,val;
	requires packedPredVal[this] && 
		(fracPredVal[this] >= 1.0) &&
		(r < 15);
	requires (forall x:Ref :: packedPredVal[x]);
	ensures packedPredVal[this] && (fracPredVal[this] >= 1.0);
	ensures (forall x:Ref :: (packedPredVal[x] == old(packedPredVal[x])));
{
	call UnpackPredVal(val[this], this);
	packedPredVal[this] := false;
	val[this] := r;
	call PackPredVal(r, this);
	packedPredVal[this]:=true;
}

procedure main()
	modifies val, next, packedPredNext, packedPredVal, fracPredVal, fracPredNext;
	requires (forall x:Ref :: packedPredVal[x]);
	requires (forall x:Ref :: packedPredNext[x]);
{
	var c : Ref;
	var a : Ref;
	var b : Ref;
  	assume (a!=b) && (b!=c) && (c!=a);
  
	call ConstructSimpleCell(2, null, c);
	packedPredVal[c] := false; 
	call PackPredVal(2, c);
	packedPredVal[c] := true;
	fracPredVal[c] := 1.0;

	call ConstructSimpleCell(2, c, a);
	packedPredNext[a] := false;
	call PackPredNext(c, a);
	packedPredNext[a] := true;
	fracPredNext[a] := 1.0;
	fracPredVal[c] := fracPredVal[c] - 0.34;

	call ConstructSimpleCell(3, c, b);

	packedPredNext[b] := false;
	call PackPredNext(c, b);
	packedPredNext[b] := true;
	fracPredNext[b] := 1.0;
	fracPredVal[c] := fracPredVal[c] - 0.34;

	call UnpackPredNext(c, a);
	packedPredNext[a] := false;

	call UnpackPredNext(c, b);
	packedPredNext[b] := false;

	fracPredVal[c] := fracPredVal[c]+0.34+0.34;

	call changeVal(c, 4);
}
