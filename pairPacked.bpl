//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique okP: PredicateTypes;
const unique pairedP: PredicateTypes;

var val: [Ref]int;
var pair: [Ref]Ref;

var packed: PackedType;
var frac: FractionType;


//global variables that keep track of the parameters of the Range predicate
//that are not values of fields
var vPairedPred: [Ref] int;
var pPairedPred: [Ref] Ref;

function PairedPred(this: Ref, val: [Ref]int, pair: [Ref]Ref, v: int, 
                    p: Ref, packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref) returns (bool);

axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, v: int, p: Ref,
       packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
       {PairedPred(this, val, pair, v, p, packed, vPairedPred, pPairedPred)}
       ((val[this] == v) && (pair[this] == p)) ==> 
        (packed[this, pairedP] && (vPairedPred[this] == v) && (pPairedPred[this] == p))
   );

//this axiom is for unpacking isPackedPairedPred
axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, v: int, p: Ref,
  packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
  {PairedPred(this, val, pair,  v, p, packed, vPairedPred, pPairedPred)}
(packed[this, pairedP] && (vPairedPred[this] == v) && (pPairedPred[this] == p))  ==>
 ((val[this] == v) && (pair[this]== p)) 
   );

//function used in the triggers for packed [_,okP]
function okPred(this:Ref, frac: FractionType, 
          packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref) returns (bool);

//used for packing predicate ok
axiom ( forall this: Ref, frac:FractionType, 
         packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref ::
         {okPred(this, frac, packed, vPairedPred, pPairedPred)}
     ( exists v:int, p:Ref :: ( packed[this, pairedP] &&
                                 (vPairedPred[this]== v) &&
                                (pPairedPred[this]== p)  && 
                               (frac[this, pairedP]>=50) &&
                               packed[p, pairedP] &&
                                 (vPairedPred[this]== v) &&
                                (pPairedPred[this]== this)  && 
                               (frac[p, pairedP]>=50) &&
                                packed[p,okP] &&
                                (frac[p, okP]>=50)
                               )
       )  ==> packed[this,okP]
      );

//used for unpacking predicate ok
axiom ( forall this: Ref, frac:FractionType,
            packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
            {okPred(this, frac, packed, vPairedPred, pPairedPred)}
     packed[this,okP] ==> 
     ( exists v:int, p:Ref :: ( packed[this, pairedP] &&
                                 (vPairedPred[this]== v) &&
                                (pPairedPred[this]== p)  && 
                               (frac[this, pairedP]>=50) &&
                               packed[p, pairedP] &&
                                 (vPairedPred[this]== v) &&
                                (pPairedPred[this]== this)  && 
                               (frac[p, pairedP]>=50) &&
                                packed[p,okP] &&
                                (frac[p, okP]>=50)
                               )
      ) 
      );



procedure increment(this: Ref)
modifies val, frac;
requires packed[this, okP];
requires frac[this, okP]>0;
ensures  packed[this, okP];
ensures frac[this, okP]>0;
{
call increment1(pair[this]);
}



procedure increment1(this: Ref)
modifies val, frac;
requires ( exists v:int, p: Ref ::
          (packed[this, pairedP] &&
          (vPairedPred[this]== v) &&
          (pPairedPred[this]== p)  )
         );
requires packed[this, okP];
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures  packed[this, okP];
ensures frac[this, okP]>0;
{
val[this]:= val[this]+1;
call increment2(pair[this]);
}



procedure increment2(this: Ref)
modifies val, frac;
requires ( exists v:int, p: Ref ::      
          (packed[this, pairedP] &&
          (vPairedPred[this]== v) &&
          (pPairedPred[this]== p)  )
         );
requires packed[this, okP];
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures ( exists v:int, p: Ref ::
          (packed[this, pairedP] &&
          (vPairedPred[this]== (v+1)) &&
          (pPairedPred[this]== p)  )
         );
ensures frac[this, pairedP]>=100;
{
assert val[this] == vPairedPred[this];
val[this]:= val[this]+1;

assert  packed[this, pairedP];
assert  vPairedPred[this]== (old(vPairedPred[this])+1);
assert  pPairedPred[this]== old(pPairedPred[this]);
         
}



