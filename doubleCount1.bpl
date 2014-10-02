//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref] int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var fracOKP: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;

const unique OKP: PredicateTypes;

//Constructor for DoubleCount that ensures OK.
//Might need to add a ConstructDoubleCount for the default constructor.
procedure ConstructDoubleCount0(this: Ref, v: int, d: int);
	ensures (val[this] == v) && 
		(dbl[this] == d) && 
		(packed[this, OKP]) && 
		(fracOKP[this] >= 100);

procedure PackOk(this:Ref);
	requires (packed[this, OKP] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOk(this:Ref);
	requires packed[this, OKP] &&
		(fracOKP[this] > 0);
	ensures (dbl[this]==val[this]*2);


procedure increment(this: Ref)
	modifies val, dbl, packed, fracOKP;
	requires packed[this, OKP]  && 
		(fracOKP[this] > 0);
	ensures  packed[this, OKP] && 
		(fracOKP[this] > 0);
{
	call UnpackOk(this);
	packed[this, OKP]:=false;
	val[this]:= val[this]+1;
	dbl[this]:= dbl[this]+2;
	call PackOk(this);
	packed[this, OKP]:=true;
}
