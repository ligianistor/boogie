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
modifies val, dbl;
requires isPackedOkPred(this, val, dbl, frac);
ensures  isPackedOkPred(this, val, dbl, frac);
{
val[this]:= val[this]+1;
dbl[this]:=dbl[this]+2;

}

//new class
//we need to put it in the same Boogie file I think

const unique shareCountP: PredicateTypes;

var dc: [Ref]Ref;

//if it refers to another class's predicate, we need to include all 
function isPackedShareCountPred(this:Ref, val: [Ref]int, dbl: [Ref]int, dc: [Ref]Ref, frac: FractionType) returns (bool);
axiom ( forall this:Ref, val: [Ref]int, dbl: [Ref]int, dc: [Ref]Ref, frac: FractionType::
      (isPackedOkPred(dc[this], val, dbl, frac) && (frac[dc[this], shareCountP]>=50)) ==> isPackedShareCountPred(this, val, dbl, dc, frac)
      );

//this axiom is for unpacking isPackedShareCountPred
axiom ( forall this:Ref, val: [Ref]int, dbl: [Ref]int, dc: [Ref]Ref, frac: FractionType::
     isPackedShareCountPred(this, val, dbl, dc, frac) ==>  (isPackedOkPred(dc[this], val, dbl, frac) && (frac[dc[this], shareCountP]>=50)) 
      );

procedure touch(this: Ref)
//even if we modify fields inside another call
//we need to mention the fields that we are modifying
modifies val, dbl;
requires isPackedShareCountPred(this, val, dbl, dc, frac);
ensures isPackedShareCountPred(this, val, dbl, dc, frac);
{
assert isPackedOkPred(dc[this], val, dbl, frac);
assert (frac[dc[this], shareCountP]>=50);
call increment(dc[this]);
assert isPackedOkPred(dc[this], val, dbl, frac);
}



