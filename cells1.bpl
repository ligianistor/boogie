//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null: Ref;

//Dependency class
const unique OKdepP: PredicateTypes;

var ce : [Ref]Ref;
var input : [Ref]int;
var packed : PackedType;
var frac : FractionType;
var oOKdepPred : [Ref]int;


//this function is only for Boogie to recognize how to instantiate the exists.
function instOKdep1(this : Ref, oOKdepPred : [Ref]int, dep1 : [Ref]Ref, o1 : int) returns (bool); 
axiom ( forall this : Ref, oOKdepPred : [Ref]int, dep1 : [Ref]Ref, o1 : int ::
        (oOKdepPred[dep1[this]] == o1) ==> instOKdep1(this, oOKdepPred, dep1, o1)
);

//this function is only for Boogie to recognize how to instantiate the exists.
function instOKdep2(this : Ref, oOKdepPred : [Ref]int, dep2 : [Ref]Ref, o2 : int) returns (bool); 
axiom ( forall this : Ref, oOKdepPred : [Ref]int, dep2 : [Ref]Ref, o2 : int ::
        (oOKdepPred[dep2[this]] == o2) ==> instOKdep2(this, oOKdepPred, dep2, o2)
);


procedure PackOKdep(this:Ref);
ensures ( ( (input[this] == 1) && 
    packed[ce[this], In1P] &&  
    (frac[ce[this], In1P] >= 50) &&
    (xIn1Pred[ce[this]] == oOKdepPred[this]) &&
    packed[ce[this], OKP] &&
    (frac[ce[this], OKP] > 0)
  ) 
    ||
  ( (input[this] == 2) && 
    packed[ce[this], In2P] &&
    (frac[ce[this], In2P] >= 50) &&
    (xIn2Pred[ce[this]] == oOKdepPred[this]) &&
    packed[ce[this], OKP] &&
    (frac[ce[this], OKP] > 0)
  )                                           
) 
==> 
packed[this, OKdepP];


procedure UnpackOKdep(this:Ref);
ensures packed[this, OKdepP]
==>
( ( (input[this] == 1) && 
    packed[ce[this], In1P] &&  
    (frac[ce[this], In1P] >= 50) &&
    (xIn1Pred[ce[this]] == oOKdepPred[this]) &&
    packed[ce[this], OKP] &&
    (frac[ce[this], OKP] > 0)
  ) 
    ||
  ( (input[this] == 2) && 
    packed[ce[this], In2P] &&
    (frac[ce[this], In2P] >= 50) &&
    (xIn2Pred[ce[this]] == oOKdepPred[this]) &&
    packed[ce[this], OKP] &&
    (frac[ce[this], OKP] > 0)
  )                                           
);


//Cell class

const unique In1P: PredicateTypes;
const unique In2P: PredicateTypes;
const unique OKP: PredicateTypes;

var in1: [Ref]int;
var in2: [Ref]int;
var out: [Ref]int;

//fields that are of type Dependency class
var dep1: [Ref]Ref;
var dep2: [Ref]Ref;

//global variables that keep track of the parameters 
//of predicates In1 and In2
var xIn1Pred: [Ref] int;
var xIn2Pred: [Ref] int;

//this is a special kind of predicate that only says what are is the value of the key in1
//and it will be handled in a special way, as in this example
procedure PackIn1(this:Ref);
ensures  (xIn1Pred[this] == in1[this]) ==> packed[this, In1P];

procedure UnpackIn1(this:Ref);
ensures packed[this, In1P] ==> (xIn1Pred[this] == in1[this]);

procedure PackIn2(this:Ref);
ensures (xIn2Pred[this] == in2[this]) ==> packed[this, In2P];


procedure UnpackIn2(this:Ref);
ensures  packed[this, In2P]  ==>  (xIn2Pred[this] == in2[this]);

procedure PackOK(this:Ref);
ensures ( 
packed[this, In1P] &&
(frac[this, In1P] >= 50) &&
(xIn1Pred[this] == in1[this]) && 
packed[dep1[this], OKdepP] &&
(frac[dep1[this], OKdepP] >= 100) &&
(oOKdepPred[dep1[this]] == out[this]) && 
(in1[this] +in2[this] == out[this]) &&
packed[this, In2P] &&
(frac[this, In2P] >= 50) &&
(xIn2Pred[this] == in2[this]) && 
packed[dep2[this], OKdepP] &&
(frac[dep2[this], OKdepP] >= 100) &&
(oOKdepPred[dep2[this]] == out[this]) 
) ==> 
packed[this, OKP];

procedure UnpackOK(this:Ref);
ensures packed[this, OKP] 
==> 
(
packed[this, In1P] &&
(frac[this, In1P] >= 50) &&
(xIn1Pred[this] == in1[this]) && 
packed[dep1[this], OKdepP] &&
(frac[dep1[this], OKdepP] >= 100) &&
(oOKdepPred[dep1[this]] == out[this]) && 
(in1[this] +in2[this] == out[this]) &&
packed[this, In2P] &&
(frac[this, In2P] >= 50) &&
(xIn2Pred[this] == in2[this]) && 
packed[dep2[this], OKdepP] &&
(frac[dep2[this], OKdepP] >= 100) &&
(oOKdepPred[dep2[this]] == out[this]) 
);


//because of this new approach that uses "packed", now the exists can be smaller in the 
//composite and only bound the maps that relate to the parameters
//
//In requires and ensures, it's not good to have exists deep inside an expression.
//boogie cannot prove even the easiest things about this kind of expressions
procedure setInputDep(this: Ref, newInput: int)
modifies in1, out, in2, xIn1Pred, xIn2Pred;
requires (dep1[this] != null) ==> packed[dep1[this], OKdepP];
requires (dep1[this] != null) ==> (frac[dep1[this], OKdepP] >= 100);
requires (dep1[this] != null) ==> (exists o1: int :: instOKdep1(this, oOKdepPred, dep1, o1) ); 

requires (dep2[this] != null) ==> packed[dep2[this], OKdepP];
requires (dep2[this] != null) ==> (frac[dep2[this], OKdepP] >= 100);
requires (dep2[this] != null) ==> (exists o2: int :: instOKdep2(this, oOKdepPred, dep2, o2) );

ensures  ((dep1[this] != null) ==>
         (packed[dep1[this], OKdepP] && (frac[dep1[this], OKdepP] >= 100) && 
         ( oOKdepPred[dep1[this]] == newInput ) ) );

ensures ((dep2[this] != null) ==>
        (packed[dep2[this], OKdepP] && (frac[dep2[this], OKdepP] >= 100) && 
        ( oOKdepPred[dep2[this]] == newInput ) ) );
{

if (dep2[this] != null)
  { 
if (input[dep2[this]] == 1) 
       {  
call UnpackOKdep(dep2[this]);

call setInput1(ce[dep2[this]], newInput); }
else { 
//we need to assume this because Java knows that 2 is the only
//possibility remaining,
//but Boogie does not know
assume (input[dep2[this]] == 2) ;

call UnpackOKdep(dep2[this]);

call setInput2(ce[dep2[this]], newInput); } 
   }


if (dep1[this] != null)
  { 
if (input[dep1[this]] == 1) 
       {
call UnpackOKdep(dep1[this]);

call setInput1(ce[dep1[this]], newInput);
}
else 
       { 
//we need to assume this because Java knows that 2 is the only
//possibility remaining,
//but Boogie does not know
assume (input[dep1[this]] == 2) ;

assert packed[dep1[this], OKdepP];
call UnpackOKdep(dep1[this]);

call setInput2(ce[dep1[this]], newInput);
} 
}

}


procedure setInput1(this: Ref, x: int)
modifies in1, out, in2, xIn1Pred, xIn2Pred;
requires packed[this, In1P];
requires frac[this, In1P] >= 50;
requires packed[this, OKP];
requires frac[this, OKP]>0;
ensures packed[this, OKP];
ensures frac[this, OKP]>0;
ensures packed[this, In1P];
ensures frac[this, In1P] >= 50;
ensures xIn1Pred[this] == x;
{
call UnpackOK(this);


in1[this] := x;
xIn1Pred[this] := x;
//whenever a change is made to in1[this], xIn1Pred[this] has to be modified (informed).
//This is in this case when the predicate In1 only refers to this.in1.
//This is a special case and we take care of it as above, maybe it will work more generally
//also, in other cases.
//Otherwise, if we don't do as above, how will xIn1Pred know that its value has changed?
out[this] := in1[this] + in2[this];

//exists only works when there it's like this: exists o:..:: function 
//where "function" is a single function, not an expression.
//We have to find an automatic way of coming up with a way to enclose the expressions
//after the exists in a predicate o their own.
//Maybe we need to do an initial translation from object propositions into Boogie,
//and then a second translation, that refines the first.
//The second translation would be from Boogie 1 to Boogie 2.
//When trying to prove that some value exists, and you have an example of an instance that 
//works as that value, *everything* has to be done in the context of the functions.


call setInputDep(this, out[this]);

//we have this for now, but we can just remove this@1/2 In1(x) from the postcondition of the method.
//We can just ensure that the invariant holds.
assume xIn1Pred[this] == x;
//maybe we need to call the Pack procedure
call PackOK(this);

}


procedure setInput2(this: Ref, x: int)
modifies in1, out, in2, xIn1Pred, xIn2Pred;
requires packed[this, In2P];
requires frac[this, In2P] >= 50;

//maybe this should be exists y...xIn2Pred.. ==y
//or maybe I should take it out altogether because it makes the proof more
//difficult to write and the understand
//We don't need this because it doesn't really mean anything.
//This is a special case for In1 and In2
requires packed[this, OKP];
requires frac[this, OKP]>0;
ensures packed[this, OKP];
ensures frac[this, OKP]>0;
ensures packed[this, In2P];
ensures frac[this, In2P] >= 50;
ensures xIn2Pred[this] == x;
{
call UnpackOK(this);

in2[this] := x;
xIn2Pred[this] := x;

out[this] := in1[this] + in2[this];

call setInputDep(this, out[this]);


//maybe removed
assume xIn2Pred[this] == x;
call PackOK(this);
}
