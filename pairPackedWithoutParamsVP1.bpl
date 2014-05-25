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
procedure PackPaired(this:Ref);
ensures ((vPairedPred[this] == val[this]) && (pPairedPred[this] == pair[this])) ==> 
        packed[this, pairedP];

procedure UnpackPaired(this:Ref);
ensures packed[this, pairedP]   ==>
 ((vPairedPred[this] == val[this]) && (pPairedPred[this] == pair[this]));

procedure PackOK(this:Ref);
ensures (
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
==> packed[this,okP];

procedure UnpackOK(this:Ref);
ensures packed[this,okP] ==> 
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
);

//used for packing predicate ok
//the automatic rule is that wherever we see v, we replace it 
//with val[this] and wherever we see p, we replace it with pair[this];
//especially if it's in an enclosing exists statement.
//then we have to add the global variables val and pair that we added to the 
//list of parameters of the axiom or function respectively.
//Once v has appeared in connection with this@1/2 Paired(v,p)
//we know that v is val[this]



procedure increment(this: Ref)
modifies val, frac;
requires packed[this, okP];
requires frac[this, okP]>0;
ensures  packed[this, okP];
ensures frac[this, okP]>0;
{
call UnpackOK(this);

//maybe we need to pack, or unpack something before this call

call increment1(pair[this]);

call PackOK(this);
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
call UnpackPaired(this);
//maybe above is Pack.., not sure

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
val[this]:= val[this]+1;

call PackPaired(this);
        
}



