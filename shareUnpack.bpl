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

axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, frac: FractionType, packed: PackedType::
      (dbl[this]==val[this]*2) ==> packed[this, okP]
      );

//this axiom is for unpacking okPred
axiom ( forall this: Ref, val: [Ref]int, dbl: [Ref]int, frac:FractionType, packed: PackedType::
       packed[this, okP] ==> (dbl[this]==val[this]*2) 
      );


procedure increment(this: Ref)
modifies val, dbl;
requires packed[this, okP];
ensures  packed[this, okP];
{
val[this]:= val[this]+1;
dbl[this]:=dbl[this]+2;
}

//new class
//we need to put it in the same Boogie file

const unique shareCountP: PredicateTypes;

var dc: [Ref]Ref;

//we only need this kind when we are not talking about fields
//like in the case of Range, where 0, 10 are external parameters
//and then, since they are global variables
//they have to go in each predicate that uses them
//
//we know that when packed[dc[this],okP], the second parameter will be val[dc[this]]
//
//if we write some other stucture like below it would be like writing 
//val[this] == val[this]
//var param2shareCountPred: [Ref] int;

//maybe only need this for the trigger that is needed in the 
//second axiom about unpacking
function shareCountPred(this:Ref, dc: [Ref]Ref, frac: FractionType, packed: PackedType) returns (void);

axiom ( forall this:Ref, val: [Ref]int, dbl: [Ref]int, dc: [Ref]Ref, frac: FractionType, packed: PackedType::
      (packed[dc[this],okP] && 
       (frac[dc[this], okP]>=50) ) 
==> packed[this, shareCountP]
      );

//this axiom is for unpacking shareCountPred
//this seems ok, but need to add a function or a structure that keeps track of the parameters
axiom ( forall this:Ref, dc: [Ref]Ref, frac: FractionType, packed: PackedType::
     {shareCountPred(this, dc, frac, packed)}
     packed[this, shareCountP] ==>  (packed[dc[this],okP] && (frac[dc[this], okP]>=50)) 
      );




procedure touch(this: Ref)
//even if we modify fields inside another call
//we need to mention the fields that we are modifying
modifies val, dbl, packed;
requires packed[this, shareCountP];
requires shareCountPred(this, dc, frac, packed);
ensures packed[this, shareCountP];
{
assert packed[this, shareCountP];
assert (packed[this, shareCountP] ==>  (packed[dc[this],okP] && (frac[dc[this], okP]>=50)));
assert packed[dc[this],okP];
assert (frac[dc[this], okP]>=50);
call increment(dc[this]);
assert packed[dc[this],okP];
}



