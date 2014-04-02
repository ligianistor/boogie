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

//this is a special kind of predicate that only says what are the values of the keys
//and it will be handled in a special way, as in this example
function PairedPred(this: Ref, val: [Ref]int, pair: [Ref]Ref, 
         packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref) returns (bool);

axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, 
       packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
       {PairedPred(this, val, pair, packed, vPairedPred, pPairedPred)}
       ((vPairedPred[this] == val[this]) && (pPairedPred[this] == pair[this])) ==> 
        packed[this, pairedP] 
   );

//this axiom is for unpacking isPackedPairedPred
axiom (forall this: Ref, val: [Ref]int, pair: [Ref]Ref, 
  packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
  {PairedPred(this, val, pair,  packed, vPairedPred, pPairedPred)}
packed[this, pairedP]   ==>
 ((vPairedPred[this] == val[this]) && (pPairedPred[this] == pair[this])) 
   );

//function used in the triggers for packed [_,okP]
function okPred(this:Ref, val: [Ref]int, pair: [Ref]Ref,  frac: FractionType, 
          packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref) returns (bool);

//used for packing predicate ok
//the automatic rule is that wherever we see v, we replace it 
//with val[this] and wherever we see p, we replace it with pair[this];
//especially if it's in an enclosing exists statement.
//then we have to add the global variables val and pair that we added to the 
//list of parameters of the axiom or function respectively.
//Once v has appeared in connection with this@1/2 Paired(v,p)
//we know that v is val[this]
axiom ( forall this: Ref, val: [Ref]int, pair: [Ref]Ref,  frac:FractionType,
         packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref ::
{okPred(this,  val, pair, frac, packed, vPairedPred, pPairedPred)}
(
packed[this, pairedP] &&
(vPairedPred[this]== val[this]) &&
(pPairedPred[this]== pair[this])  && 
(frac[this, pairedP]>=50) &&
packed[pair[this], pairedP] &&
(vPairedPred[pair[this]]== val[this]) &&
(pPairedPred[pair[this]]== this)  && 
(frac[pair[this], pairedP]>=50) &&
packed[pair[this], okP] &&
(frac[pair[this], okP]>=50)
)
==> packed[this,okP]
      );

//used for unpacking predicate ok
axiom ( forall this: Ref, val: [Ref]int, pair: [Ref]Ref,  frac:FractionType,
            packed: PackedType, vPairedPred: [Ref] int, pPairedPred: [Ref] Ref::
{okPred(this, val, pair, frac, packed, vPairedPred, pPairedPred)}
packed[this,okP] ==> 
(
packed[this, pairedP] &&
(vPairedPred[this]== val[this]) &&
(pPairedPred[this]== pair[this])  && 
(frac[this, pairedP]>=50) &&
packed[pair[this], pairedP] &&
(vPairedPred[pair[this]]== val[this]) &&
(pPairedPred[pair[this]]== this)  && 
(frac[pair[this], pairedP]>=50) &&
packed[pair[this], okP] &&
(frac[pair[this], okP]>=50)
)
       );



procedure increment(this: Ref)
modifies val, frac;
requires  okPred(this, val, pair, frac, packed, vPairedPred, pPairedPred);
requires packed[this, okP];
requires frac[this, okP]>0;
ensures  packed[this, okP];
ensures frac[this, okP]>0;
{
  
//not sure why if we put assert this doesn't hold, when for okPaired it's ok 
//to put assert
//assume  okPred(this, val, pair, frac, packed, vPairedPred, pPairedPred);
assert (packed[this, pairedP] &&
(vPairedPred[this]== val[this]) &&
(pPairedPred[this]== pair[this])  && 
(frac[this, pairedP]>=50) &&
packed[pair[this], pairedP] &&
(vPairedPred[pair[this]]== val[this]) &&
(pPairedPred[pair[this]]== this)  && 
(frac[pair[this], pairedP]>=50) &&
packed[pair[this], okP] &&
(frac[pair[this], okP]>=50) );

assert packed[pair[this], pairedP];
//we need this for the trigger part, but it doesn't 
//mean it's true in the Boolean sense
//when needing to pack or unpack, right before,
//we have to assume (or assert if possible) the trigger
assume PairedPred(pair[this], val, pair,  packed, vPairedPred, pPairedPred);

call increment1(pair[this]);
}



procedure increment1(this: Ref)
modifies val, frac;
//whenever we have v, replace it with val[this]
//better to put each requires on its own line
requires  packed[this, pairedP]; 
requires  (vPairedPred[this] == val[this]) ;
requires   (pPairedPred[this] == pair[this]);
        
requires packed[this, okP];
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures  packed[this, okP];
ensures frac[this, okP]>0;
{
val[this]:= val[this]+1;
//not sure if this is assert or assume
//and why it holds no matter what
assert PairedPred(this, val, pair,  packed, vPairedPred, pPairedPred);
assert  packed[pair[this], pairedP];
assert (vPairedPred[pair[this]]== val[pair[this]]);
assert (pPairedPred[pair[this]]== pair[pair[this]]);
assert packed[pair[this], okP];
assert frac[pair[this], okP]>0;
assert frac[pair[this], pairedP]>=50;


call increment2(pair[this]);
}



procedure increment2(this: Ref)
modifies val, frac;
requires  packed[this, pairedP] &&
          (vPairedPred[this]== val[this]) &&
          (pPairedPred[this]== pair[this]);
requires packed[this, okP];
requires frac[this, okP]>0;
requires frac[this, pairedP]>=50;
ensures   (packed[this, pairedP] &&
          (vPairedPred[this]== (old(val[this])+1)) &&
          (pPairedPred[this]== pair[this]));
ensures frac[this, pairedP]>=100;
{
assert val[this] == vPairedPred[this];
val[this]:= val[this]+1;

assert  packed[this, pairedP];
//we can insert an assert like below whenever we need to assert
//which are the parameters that we are talking about
//for the trigger to the axioms
assert PairedPred(this, val, pair,  packed, vPairedPred, pPairedPred);
assert  vPairedPred[this]== (old(vPairedPred[this])+1);
assert  pPairedPred[this]== old(pPairedPred[this]);         
}



