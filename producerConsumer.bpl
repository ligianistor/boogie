//type Ref is intended to represent object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null:Ref;
const unique RangeP:PredicateTypes;

var val: [Ref]int;
var next: [Ref]Ref;

var frac: FractionType;
var packed: PackedType;

//global variables that keep track of the parameters of the Range predicate
//that are not values of fields
var xRangePred: [Ref] int;
var yRangePred: [Ref] int;

function RangePred(this: Ref, val:[Ref]int, next:[Ref]Ref, frac: FractionType, x:int, y:int , packed: PackedType,
   xRangePred: [Ref] int, yRangePred: [Ref] int) returns (bool);
   

//these axioms are for packing the Range predicate
axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref , packed: PackedType, xRangePred: [Ref] int,
 yRangePred: [Ref] int :: 
 ((this != null) &&  (next[this] == null) && (val[this] >= x) && (val[this] <= y) ==> 
    (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) ) 
)); 
     

axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref, frac: FractionType, packed: PackedType,
         xRangePred: [Ref] int, yRangePred: [Ref] int :: 
 {RangePred(this,val,next,frac,x,y, packed, xRangePred, yRangePred)}
 (  (this != null) && (next[this] != null) && (val[this] >= x) && (val[this] <= y) && 
    packed[next[this], RangeP] && (xRangePred[next[this]]==x) && (yRangePred[next[this]]==y)
       ==>  (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) )  )
  );       


 axiom (forall this:Ref,  packed: PackedType:: 
     (this==null) ==> (packed[this, RangeP] ) 
     ); 
     
//this axiom is used for unpacking
     axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref, frac: FractionType, packed: PackedType,
        xRangePred: [Ref] int, yRangePred: [Ref] int :: 
{RangePred(this,val,next,frac,x,y, packed, xRangePred, yRangePred)}
 ( (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) ) ==>
    ( (this != null) &&
       (val[this] >= x) &&
        (val[this] <= y) && 
        packed[next[this], RangeP] &&
         (xRangePred[next[this]]==x) &&
          (yRangePred[next[this]]==y) &&
          RangePred(this,val,next,frac,0,10, packed, xRangePred, yRangePred)
    ) 
  ) 
  );  

//modulo is not implemented in Boogie
//so its properties have to be described  
function modulo(x:int, y:int) returns (int);
  axiom (forall x:int, y:int :: {modulo(x,y)} 
    ((0<=x) &&(0<y) ==> (0<= modulo(x,y) ) && (modulo(x,y)<y) )
    &&
    ((0<=x) &&(y<0) ==> (0<= modulo(x,y) ) && (modulo(x,y)<-y) )
    &&
    ((x<=0) &&(0<y) ==> (-y<= modulo(x,y) ) && (modulo(x,y)<=0) )
    &&
    ((x<=0) &&(y<0) ==> (y<= modulo(x,y) ) && (modulo(x,y)<=0) )
   );    

procedure addModulo11(this: Ref, x:int) 
modifies val, packed;
//need to put this in for modulo 
requires this!=null;
//requires val[this]>=0;
requires x>=0;
requires RangePred(this,val,next,frac,0,10, packed, xRangePred, yRangePred);
//this could be 100 here
//requires frac[this, RangeP]>=50;
requires xRangePred[this]==0; 
requires yRangePred[this]==10;
requires packed[this, RangeP];
ensures packed[this, RangeP];
ensures xRangePred[this]==0; 
ensures yRangePred[this]==10;
//ensures frac[this, RangeP]>=50;
{ 
 val[this] := modulo((val[this]+x),11);
 
  if (next[this] != null )
  { 
assert (packed[this, RangeP] && (xRangePred[this]==0) && (yRangePred[this]==10) ) ==>
     ( (this != null) &&
       (val[this] >= 0) &&
        (val[this] <= 10) && 
        packed[next[this], RangeP] &&
         (xRangePred[next[this]]==0) &&
          (yRangePred[next[this]]==10)
    )  ;
     
//assert val[next[this]]>=0;
assert xRangePred[next[this]]==0; 
assert yRangePred[next[this]]==10;
assert packed[next[this], RangeP]; 
assert (val[this] >= 0);
assert (val[this] <= 10);     
call addModulo11(next[this], x);
assert packed[next[this], RangeP]; 
  }
assert  packed[next[this], RangeP]; 
 
assert this != null;
//next[this] can be null or not
assume (next[this] != null);

  //val[this] was not modified
  //but Boogie does not know that
assume old(val[this])==val[this];
 
//we need this assume to say which are the parameters that 
//we are packing with
//it does not mean that RangePred is true in the Boolean sense
//it's just for the parameters 

//we did not need the frame axiom as in previous encoding of the range example
assume RangePred(this,val,next,frac,0,10, packed, xRangePred, yRangePred);
assert packed[this, RangeP]; 
  }


//===========================================================================
//consumer class
var startJobs: [Ref]Ref;

var xConsumeInRangePred: [Ref] int;
var yConsumeInRangePred: [Ref] int;
const unique ConsumeInRangeP:PredicateTypes;

function ConsumeInRangePred(this:Ref, x:int, y:int,  startJobs: [Ref]Ref, 
              xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int) returns (bool);

//this axiom is for packing the ConsumeInRange predicate
axiom (forall this:Ref, x:int, y:int,  startJobs: [Ref]Ref, 
              xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int :: 
{ConsumeInRangePred(this, x, y,  startJobs, xConsumeInRangePred, yConsumeInRangePred, packed, xRangePred, yRangePred)}
 (packed[startJobs[this], RangeP] && (xRangePred[startJobs[this]] == x) && (yRangePred[startJobs[this]] == y )==> 
    (packed[this, ConsumeInRangeP] && (xConsumeInRangePred[this]==x) && (yConsumeInRangePred[this]==y) ) 
)); 

//this axiom is for unpacking the ConsumeInRange predicate
axiom (forall this:Ref, x:int, y:int,  startJobs: [Ref]Ref, 
              xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int :: 
{ConsumeInRangePred(this, x, y,  startJobs, xConsumeInRangePred, yConsumeInRangePred, packed, xRangePred, yRangePred)}
 (packed[this, ConsumeInRangeP] && (xConsumeInRangePred[this]==x) && (yConsumeInRangePred[this]==y)==> 
    ( packed[startJobs[this], RangeP] && (xRangePred[startJobs[this]] == x ) && (yRangePred[startJobs[this]] == y ) ) 
)); 
    

procedure consume(this: Ref) 
modifies startJobs, packed;
requires packed[this, ConsumeInRangeP];
ensures packed[this, ConsumeInRangeP];
{
if (startJobs[this] != null)
{
startJobs[this] := startJobs[next[this]];
}
  
}

//===========================================================================
//producer class
var startSmallJobs: [Ref]Ref;
var startLargeJobs: [Ref]Ref;
var endSmallJobs: [Ref]Ref;
var endLargeJobs: [Ref]Ref;

const unique BothInRangeP:PredicateTypes;

function BothInRangePred(this:Ref,  startSmallJobs: [Ref]Ref, startLargeJobs: [Ref]Ref,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int) returns (bool);

//this axiom is for packing the BothInRange predicate
axiom (forall this:Ref,  startSmallJobs: [Ref]Ref, startLargeJobs: [Ref]Ref,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int :: 
{BothInRangePred(this,  startSmallJobs, startLargeJobs, packed, xRangePred, yRangePred)}
 (packed[startSmallJobs[this], RangeP] && (xRangePred[startSmallJobs[this]] == 0) && (yRangePred[startSmallJobs[this]] == 10) 
&& packed[startLargeJobs[this], RangeP] && (xRangePred[startLargeJobs[this]] == 11) && (yRangePred[startLargeJobs[this]] == 100) 
==> 
    (packed[this, BothInRangeP]) 
)); 

//this axiom is for unpacking the BothInRange predicate
axiom (forall this:Ref,  startSmallJobs: [Ref]Ref, startLargeJobs: [Ref]Ref,
              packed: PackedType, xRangePred: [Ref] int, yRangePred: [Ref] int ::
{BothInRangePred(this,  startSmallJobs, startLargeJobs, packed, xRangePred, yRangePred)} 
 ((packed[this, BothInRangeP])
==> 
packed[startSmallJobs[this], RangeP] && (xRangePred[startSmallJobs[this]] == 11) && (yRangePred[startSmallJobs[this]] == 100) 
&& packed[startLargeJobs[this], RangeP] && (xRangePred[startLargeJobs[this]] == 11) && (yRangePred[startLargeJobs[this]] == 100)      
)); 

procedure produce(this: Ref)
modifies packed, startSmallJobs, endSmallJobs, next;
modifies startLargeJobs, endLargeJobs, val;
requires packed[this, BothInRangeP];
ensures packed[this, BothInRangeP];
{
var r: int;
//create a new Link object called l
var l: Ref;

assume ((r >= 0) && (r <= 100));
val[l]:=r;
next[l]:=null;
if (r<=10)
{ 
 if (startSmallJobs[this]==null)
 {
  startSmallJobs[this] := l;
  endSmallJobs[this] := l;
 }
 else 
 {
  next[endSmallJobs[this]] := l;
  endSmallJobs[this] := l;
 }
}
else
{ 
  if (startLargeJobs[this]==null)
 {
  startLargeJobs[this] := l;
  endLargeJobs[this] := l;
 }
 else 
 {
  next[endLargeJobs[this]] := l;
  endLargeJobs[this] := l;
 }
}

}

//===========================================================================
//control class
var prod1: [Ref]Ref;
var prod2: [Ref]Ref;
var cons1: [Ref]Ref;
var cons2: [Ref]Ref;

const unique WorkingSystemP:PredicateTypes;

function WorkingSystemPred(this:Ref, prod1:[Ref]Ref,  prod2: [Ref]Ref,  cons1: [Ref]Ref,  cons2: [Ref]Ref,
              packed: PackedType, xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int) returns (bool);

//this axiom is for packing the WorkingSystem predicate
axiom (forall this:Ref, prod1:[Ref]Ref,  prod2: [Ref]Ref,  cons1: [Ref]Ref,  cons2: [Ref]Ref,
              packed: PackedType, xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int :: 
{WorkingSystemPred(this, prod1,  prod2,  cons1,  cons2,
              packed, xConsumeInRangePred, yConsumeInRangePred)}
 (packed[prod1[this], BothInRangeP] && packed[prod2[this], BothInRangeP] 
&& packed[cons1[this], ConsumeInRangeP] && packed[cons2[this], ConsumeInRangeP] 
&& (xConsumeInRangePred[cons1[this]] == 0) && (yConsumeInRangePred[cons1[this]] == 10)
&& (xConsumeInRangePred[cons2[this]] == 11) && (yConsumeInRangePred[cons2[this]] == 100)
==> 
    (packed[this, WorkingSystemP]) 
)); 

//this axiom is for unpacking the WorkingSystem predicate
axiom (forall this:Ref, prod1:[Ref]Ref,  prod2: [Ref]Ref,  cons1: [Ref]Ref,  cons2: [Ref]Ref,
              packed: PackedType, xConsumeInRangePred: [Ref] int, yConsumeInRangePred: [Ref] int :: 
{WorkingSystemPred(this, prod1,  prod2,  cons1,  cons2,
              packed, xConsumeInRangePred, yConsumeInRangePred)}
 ((packed[this, WorkingSystemP]) 
==> 
packed[prod1[this], BothInRangeP] && packed[prod2[this], BothInRangeP] 
&& packed[cons1[this], ConsumeInRangeP] && packed[cons2[this], ConsumeInRangeP] 
&& (xConsumeInRangePred[cons1[this]] == 0) && (yConsumeInRangePred[cons1[this]] == 10)
&& (xConsumeInRangePred[cons2[this]] == 11) && (yConsumeInRangePred[cons2[this]] == 100)   
)); 

procedure makeActive(this:Ref, i:int)
modifies packed, startSmallJobs, endSmallJobs, next;
modifies startLargeJobs, endLargeJobs, startJobs, val;
requires packed[this, WorkingSystemP];
ensures packed[this, WorkingSystemP];
{
var r: int;
assume ((r >= 0) && (r <= 3));
if (r == 0) 
{ call produce(prod1[this]); }
else if (r == 1) 
     { call produce(prod2[this]); }
     else if (r == 2)
          { call consume(cons1[this]);}
          else { call consume(cons2[this]);} 
if (i>0) 
{call makeActive(this, i-1);}
}