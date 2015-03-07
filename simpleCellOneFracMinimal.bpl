type Ref;
const null: Ref;

var val: [Ref]int;
var next: [Ref]Ref;
var packedPredNext: [Ref] bool;
var fracPredNext: [Ref] real;
var packedPredVal: [Ref] bool;
var fracPredVal: [Ref] real;
 
procedure ConstructSimpleCell(val1: int, next1: Ref, this: Ref);
	ensures (val[this] == val1) && 
		(next[this] == next1);

procedure PackPredVal(this: Ref);
	requires (packedPredVal[this] == false) && 
		(val[this] < 15);

procedure UnpackPredVal(this: Ref);
	requires packedPredVal[this] &&
		(fracPredVal[this] > 0.0);
	ensures val[this] < 15;

procedure PackPredNext(this: Ref);
	requires (fracPredVal[next[this]] == 0.34) &&
		(packedPredNext[this] == false);

procedure UnpackPredNext(this: Ref);
	requires packedPredNext[this] &&
		(fracPredNext[this] > 0.0);
	ensures	(fracPredVal[next[this]] == 0.34);

procedure changeVal(this: Ref, r: int)
	modifies packedPredVal,val;
	requires packedPredVal[this] && 
		(fracPredVal[this] == 1.0) &&
		(r < 15);
	requires (forall x:Ref :: packedPredVal[x]);
	requires (forall x:Ref :: packedPredNext[x]);
	ensures packedPredVal[this] &&
		(fracPredVal[this] == 1.0);
	ensures (forall x:Ref :: (packedPredVal[x] == old(packedPredVal[x])));
{
	call UnpackPredVal(this);
	packedPredVal[this] := false;
	val[this] := r;
	call PackPredVal(this);
	packedPredVal[this]:=true;
}

procedure main()
	modifies val, packedPredNext, packedPredVal, fracPredVal, fracPredNext;
	requires (forall x:Ref :: packedPredVal[x]);
	requires (forall x:Ref :: packedPredNext[x]);
	
{
	var c : Ref;
	var a : Ref;
	var b : Ref;

	call ConstructSimpleCell(2,null,c);
	packedPredVal[c] := true;
	fracPredVal[c] := 1.0;

	call ConstructSimpleCell(2,c,a);
	packedPredNext[a] := true;
	fracPredNext[a] := 1.0;
	fracPredVal[c] := fracPredVal[c] - 0.34;
	
	call ConstructSimpleCell(3,c,b);
	packedPredNext[b] := true;
	fracPredNext[b] := 1.0;
	fracPredVal[c] := fracPredVal[c] - 0.34;

	call UnpackPredNext(a);
	packedPredNext[a] := false;

	call UnpackPredNext(b);
	packedPredNext[b] := false;

	fracPredVal[c] := fracPredVal[c]+0.34+0.34;

	call changeVal(c, 4);
}
