type Ref;
type FractionType = [Ref] real;
type PackedType = [Ref] bool;
//divide packed for each PredicateType
//In Boogie it is always better for things to be as separate as 
//possible because of the modifies.
var packedOK: PackedType;
var fracOK: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;


procedure ConstructDoubleCount(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1);

procedure PackOK(this:Ref);
	requires (packedOK[this] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOK(this:Ref);
	requires packedOK[this] &&
		(fracOK[this] > 0.0);
	ensures (dbl[this]==val[this]*2);

procedure increment(this: Ref)
	modifies val, dbl, packedOK;
	requires packedOK[this]  && 
		(fracOK[this] > 0.0);
	requires (forall x:Ref :: packedOK[x]);
	ensures  packedOK[this] && 
		(fracOK[this] > 0.0);
	ensures (forall x:Ref :: (packedOK[x] == old(packedOK[x])));
{
	call UnpackOK(this);
	packedOK[this] := false;
	val[this] := val[this]+1;
	dbl[this] := dbl[this]+2;
	call PackOK(this);
	packedOK[this] := true;
}
