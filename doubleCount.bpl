//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type UnpackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique okP: PredicateTypes;

var val: [Ref]int;
var dbl: [Ref]int;
var unpacked: UnpackedType;
var frac: FractionType;


function isPackedOkPred(this:Ref, val: [Ref]int, dbl: [Ref]int, frac: FractionType) returns (bool);
axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, frac:FractionType::
      (dbl[this]==val[this]*2) ==> isPackedOkPred(this, val, dbl, frac)
      );

//this axiom is for unpacking isPackedOkPred
axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, frac:FractionType::
      isPackedOkPred(this, val, dbl, frac) ==> (dbl[this]==val[this]*2) 
      );


procedure increment(this: Ref)
modifies val, dbl, frac, unpacked;
requires isPackedOkPred(this, val, dbl, frac);
ensures  isPackedOkPred(this, val, dbl, frac);
{
val[this]:= val[this]+1;
dbl[this]:=dbl[this]+2;

}




