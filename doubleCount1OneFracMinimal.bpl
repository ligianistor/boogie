type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var frac: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;
const unique OKP: PredicateTypes;

procedure ConstructDoubleCountOKP(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1) && 
		(packed[this, OKP]) && 
		(frac[this, OKP] >= 100);

procedure ConstructDoubleCount(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1);

procedure PackOK(this:Ref);
	requires (packed[this, OKP] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOK(this:Ref);
	requires packed[this, OKP] &&
		(frac[this, OKP] >= 1);
	ensures (dbl[this]==val[this]*2);


procedure increment(this: Ref)
	modifies val, dbl, packed, frac;
	requires packed[this, OKP]  && 
		(frac[this, OKP] >= 1);
	ensures  packed[this, OKP] && 
		(frac[this, OKP] >= 1);
{
	call UnpackOK(this);
	packed[this, OKP]:=false;
	val[this]:= val[this]+1;
	dbl[this]:= dbl[this]+2;
	call PackOK(this);
	packed[this, OKP]:=true;
}
