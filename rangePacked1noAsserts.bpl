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

//after calling procedures PackRangeNextNull, any kind 
//of Pack procedures, I have to do
//packed[this, rangeP]:=true

procedure PackRangeNextNull(this:Ref, x:int, y:int);
requires (this != null) &&  (next[this] == null) && (val[this] >= x) && (val[this] <= y);
ensures (xRangePred[this]==x) && (yRangePred[this]==y);


procedure PackRangeNextNotNull(this:Ref, x:int, y:int);
requires (this != null) && (next[this] != null) && (val[this] >= x) && (val[this] <= y) && 
    packed[next[this], RangeP] && (xRangePred[next[this]]==x) && (yRangePred[next[this]]==y);
ensures (xRangePred[this]==x) && (yRangePred[this]==y);

procedure PackThisNull(this:Ref);
requires this==null;

procedure UnpackRange(this:Ref, x:int, y:int);
requires packed[this, RangeP] && (xRangePred[this]==x) && (yRangePred[this]==y);
ensures
(this != null) &&
(val[this] >= x) &&
(val[this] <= y) && 
packed[next[this], RangeP] &&
(xRangePred[next[this]]==x) &&
(yRangePred[next[this]]==y);
 

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
modifies val, packed, xRangePred;
//need to put this in for modulo 
requires this!=null;
//requires x>=0;
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
packed[this, RangeP]:=false;
assume (this != next[this]);
val[this] := modulo((val[this]+x),11);

if (next[this] != null )
  { 
call addModulo11(next[this], x);
  }

  //val[this] was not modified
  //but Boogie does not know that
assume old(val[this])==val[this];
assume next[this]==null;
call PackRangeNextNull(this, 0, 10);
assume next[this]!=null;
call PackRangeNextNotNull(this, 0, 10);
packed[this,RangeP]:=true;
  }
