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

procedure PackRangeNextNull(this:Ref, x:int, y:int);
ensures ((this != null) &&  (next[this] == null) && (val[this] >= x) && (val[this] <= y) ==> 
    (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) ) );


procedure PackRangeNextNotNull(this:Ref, x:int, y:int);
ensures  (  (this != null) && (next[this] != null) && (val[this] >= x) && (val[this] <= y) && 
    packed[next[this], RangeP] && (xRangePred[next[this]]==x) && (yRangePred[next[this]]==y)
       ==>  (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) )  );

procedure PackThisNull(this:Ref);
ensures  (this==null) ==> (packed[this, RangeP] );

procedure UnpackRange(this:Ref, x:int, y:int);
ensures ( (packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y) ) ==>
    ( (this != null) &&
       (val[this] >= x) &&
        (val[this] <= y) && 
        packed[next[this], RangeP] &&
         (xRangePred[next[this]]==x) &&
          (yRangePred[next[this]]==y)));
 

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
call UnpackRange(this, 0, 10);
 val[this] := modulo((val[this]+x),11);
 
  if (next[this] != null )
  { 
call addModulo11(next[this], x);
  }

  //val[this] was not modified
  //but Boogie does not know that
assume old(val[this])==val[this];
call PackRangeNextNull(this, 0, 10);
call PackRangeNextNotNull(this, 0, 10);
  }


//===========================================================================
//this might need some work
//consumer class
var startJobs: [Ref]Ref;

var xConsumeInRangePred: [Ref] int;
var yConsumeInRangePred: [Ref] int;
const unique ConsumeInRangeP:PredicateTypes;

procedure PackConsumeInRange(this:Ref);
ensures packed[startJobs[this], RangeP] && (xRangePred[startJobs[this]] == xConsumeInRangePred[this]) &&
 (yRangePred[startJobs[this]] == yConsumeInRangePred[this] )==> 
    packed[this, ConsumeInRangeP];


procedure UnpackConsumeInRange(this:Ref);
ensures packed[this, ConsumeInRangeP]==> 
    packed[startJobs[this], RangeP] && (xRangePred[startJobs[this]] == xConsumeInRangePred[this] ) &&
 (yRangePred[startJobs[this]] == yConsumeInRangePred[this] );

    

procedure consume(this: Ref) 
modifies startJobs, packed;
requires packed[this, ConsumeInRangeP];
ensures packed[this, ConsumeInRangeP];
{
call UnpackConsumeInRange(this);
if (startJobs[this] != null)
{
startJobs[this] := startJobs[next[this]];
}
call PackConsumeInRange(this);
  
}

//===========================================================================
//producer class
var startSmallJobs: [Ref]Ref;
var startLargeJobs: [Ref]Ref;
var endSmallJobs: [Ref]Ref;
var endLargeJobs: [Ref]Ref;

const unique BothInRangeP:PredicateTypes;

procedure PackBothInRange(this:Ref);
ensures packed[startSmallJobs[this], RangeP] && (xRangePred[startSmallJobs[this]] == 0) && (yRangePred[startSmallJobs[this]] == 10) 
&& packed[startLargeJobs[this], RangeP] && (xRangePred[startLargeJobs[this]] == 11) && (yRangePred[startLargeJobs[this]] == 100) 
==> 
packed[this, BothInRangeP];


procedure UnpackBothInRange(this:Ref);
ensures 
packed[this, BothInRangeP]
==> 
packed[startSmallJobs[this], RangeP] && (xRangePred[startSmallJobs[this]] == 11) && (yRangePred[startSmallJobs[this]] == 100) 
&& packed[startLargeJobs[this], RangeP] && (xRangePred[startLargeJobs[this]] == 11) && (yRangePred[startLargeJobs[this]] == 100);


procedure produce(this: Ref)
modifies packed, startSmallJobs, endSmallJobs, next;
modifies startLargeJobs, endLargeJobs, val;
requires packed[this, BothInRangeP];
ensures packed[this, BothInRangeP];
{

var r: int;
//create a new Link object called l
var l: Ref;
call UnpackBothInRange(this);
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
call PackBothInRange(this);
}

//===========================================================================
//control class
var prod1: [Ref]Ref;
var prod2: [Ref]Ref;
var cons1: [Ref]Ref;
var cons2: [Ref]Ref;

const unique WorkingSystemP:PredicateTypes;

procedure PackWorkingSystem(this:Ref);
ensures (packed[prod1[this], BothInRangeP] && packed[prod2[this], BothInRangeP] 
&& packed[cons1[this], ConsumeInRangeP] && packed[cons2[this], ConsumeInRangeP] 
&& (xConsumeInRangePred[cons1[this]] == 0) && (yConsumeInRangePred[cons1[this]] == 10)
&& (xConsumeInRangePred[cons2[this]] == 11) && (yConsumeInRangePred[cons2[this]] == 100)
==> 
    (packed[this, WorkingSystemP]) 
);


procedure UnpackWorkingSystem(this:Ref);
ensures ((packed[this, WorkingSystemP]) 
==> 
packed[prod1[this], BothInRangeP] && packed[prod2[this], BothInRangeP] 
&& packed[cons1[this], ConsumeInRangeP] && packed[cons2[this], ConsumeInRangeP] 
&& (xConsumeInRangePred[cons1[this]] == 0) && (yConsumeInRangePred[cons1[this]] == 10)
&& (xConsumeInRangePred[cons2[this]] == 11) && (yConsumeInRangePred[cons2[this]] == 100)   
);


procedure makeActive(this:Ref, i:int)
modifies packed, startSmallJobs, endSmallJobs, next;
modifies startLargeJobs, endLargeJobs, startJobs, val;
requires packed[this, WorkingSystemP];
ensures packed[this, WorkingSystemP];
{
var r: int;
call UnpackWorkingSystem(this);
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

call PackWorkingSystem(this);
}