//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique okP: PredicateTypes;

var val: [Ref]int;
var dbl: [Ref]int;
var packed: PackedType;
var frac: FractionType;

procedure PackOK(this:Ref);
ensures (dbl[this]==val[this]*2) ==> packed[this, okP];

procedure UnpackOK(this:Ref);
ensures packed[this, okP] ==> (dbl[this]==val[this]*2);


procedure increment(this: Ref)
modifies val, dbl, packed;
requires packed[this, okP];
requires frac[this, okP] >0;
ensures  packed[this, okP];
ensures frac[this, okP] >0;
{
call UnpackOK(this);
packed[this, okP]:=false;
val[this]:= val[this]+1;
dbl[this]:=dbl[this]+2;
call PackOK(this);
}

