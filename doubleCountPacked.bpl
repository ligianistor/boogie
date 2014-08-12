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

function okPred(this:Ref, val: [Ref]int, dbl: [Ref]int, packed: PackedType) returns (bool);

axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, packed: PackedType::
       {okPred(this, val, dbl, packed)}
      (dbl[this]==val[this]*2) ==> packed[this, okP]
      );

//this axiom is for unpacking predicate ok
axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, packed: PackedType::
       {okPred(this, val, dbl, packed)}
      packed[this, okP] ==> (dbl[this]==val[this]*2) 
      );

procedure increment(this: Ref)
modifies val, dbl, packed;
requires packed[this, okP];
requires frac[this, okP] >0;
ensures  packed[this, okP];
ensures frac[this, okP] >0;
{
assume okPred(this, val, dbl, packed);
packed[this, okP]:=false;
val[this]:= val[this]+1;
dbl[this]:=dbl[this]+2;
//we have to assume this, although it has no meaning,
//right before unpacking something, or right before packing something.
//It's for Boogie to know which axiom to apply.
assume okPred(this, val, dbl, packed);
//I need to deal with the fractions, how that works.
//I might need a small example for that.

}

