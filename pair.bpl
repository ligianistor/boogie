//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type UnpackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique okP: PredicateTypes;
const unique pairedP: PredicateTypes;

var val: [Ref]int;
var pair: [Ref]Ref;

var unpacked: UnpackedType;
var frac: FractionType;

function isPackedPairedPred(this: Ref, val: [Ref]int, pair: [Ref]Ref, frac: FractionType, v: int, p: Ref) returns (bool);
axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, frac: FractionType, v: int, p: Ref::
       ((val[this] == v) && (pair[this] == p)) ==> isPackedPairedPred(this, val, pair, frac, v, p)
   );

//this axiom is for unpacking isPackedPairedPred
axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, frac: FractionType, v: int, p: Ref::
        isPackedPairedPred(this, val, pair, frac, v, p) ==> ((val[this] == v) && (pair[this]== p)) 
   );

function isPackedOkPred(this:Ref, val: [Ref]int, pair: [Ref]Ref, frac: FractionType) returns (bool);
axiom ( forall this: Ref, val: [Ref]int, pair: [Ref]Ref, frac:FractionType::
     ( exists v:int, p:Ref :: ( isPackedPairedPred(this, val, pair, frac,v, p) && 
                               (frac[this, pairedP]>=50) &&
                               isPackedPairedPred(p, val, pair, frac, v, this) &&
                               (frac[p, pairedP]>=50) &&
                                isPackedOkPred(p, val, pair, frac) &&
                                (frac[p, okP]>=50)
                               )
       )  ==> isPackedOkPred(this, val, pair, frac)
      );

//this axiom is for unpacking isPackedOkPred
axiom ( forall this: Ref, val: [Ref]int, pair: [Ref]Ref, frac:FractionType::
      isPackedOkPred(this, val, pair, frac) ==> 
      ( exists v:int, p:Ref :: ( isPackedPairedPred(this, val, pair, frac,v, p) && 
                               (frac[this, pairedP]>=50) &&
                               isPackedPairedPred(p, val, pair, frac, v, this) &&
                               (frac[p, pairedP]>=50) &&
                                isPackedOkPred(p, val, pair, frac) &&
                                (frac[p, okP]>=50)
                               )
       ) 
      );



procedure increment(this: Ref)
modifies val, frac;
requires isPackedOkPred(this, val, pair, frac);
requires frac[this, okP]>0;
ensures  isPackedOkPred(this, val, pair, frac);
ensures frac[this, okP]>0;
{
call increment1(pair[this]);
}



procedure increment1(this: Ref)
modifies val, frac;
requires ( exists v:int, p: Ref ::
          isPackedPairedPred(this, val, pair, frac, v, p)
         );
requires isPackedOkPred(this, val, pair, frac);
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures  isPackedOkPred(this, val, pair, frac);
ensures frac[this, okP]>0;
{
val[this]:= val[this]+1;
call increment2(pair[this]);
}



procedure increment2(this: Ref)
modifies val, frac;
requires ( exists v:int, p: Ref ::
          isPackedPairedPred(this, val, pair, frac, v, p)
         );
requires isPackedOkPred(this, val, pair, frac);
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures ( exists v:int, p: Ref ::
          isPackedPairedPred(this, val, pair, frac, v, p)
         );
ensures frac[this, pairedP]>=100;
{
val[this]:= val[this]+1;
}



