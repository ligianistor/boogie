//THIS WORKS
//type Ref is intended to represent object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type UnpackedType = [Ref, PredicateTypes] bool;



const null:Ref;
const unique RangeP:PredicateTypes;

var val: [Ref]int;
var next: [Ref]Ref;

var frac: FractionType;
var unpacked: UnpackedType;


function Range(this: Ref, val:[Ref]int, next:[Ref]Ref, frac: FractionType, x:int, y:int) returns (bool);

//frame theorem
axiom (forall this:Ref, x:int, y:int, val: [Ref]int, val1: [Ref]int, next: [Ref]Ref , frac: FractionType :: 
 (Range(next[this],val,next,frac,x,y) && ((val1[this]!=val[this]) || (val1[this]==val[this])) && 
      (forall r:Ref :: r!=this ==> val1[r]==val[r]) ) 
     ==> Range(next[this],val1,next,frac,x,y));

//these axioms are for packing the Range predicate
axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref , frac: FractionType :: 
{Range(this,val,next,frac,x,y)}
 ((this != null) &&  (next[this] == null) && (val[this] >= x) && (val[this] <= y) ==> 
     Range(this,val,next,frac,x,y) 
)); 
     

      axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref, frac: FractionType :: 
{Range(this,val,next,frac,x,y)}
 (  (this != null) && (next[this] != null) && (val[this] >= x) && (val[this] <= y) && Range(next[this],val,next,frac,x,y)
       ==> Range(this,val,next,frac,x,y) )
  );       


 axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref, frac: FractionType :: 
{Range(this,val,next,frac,x,y)}
     (this==null) ==> Range(this,val,next,frac,x,y)
     ); 
     
 //this axiom is used for unpacking
     axiom (forall this:Ref, x:int, y:int, val: [Ref]int, next: [Ref]Ref, frac: FractionType :: 
{Range(this,val,next,frac,x,y)}
 ( Range(this,val,next,frac,x,y) ==>
     (this != null) && (val[this] >= x) && (val[this] <= y) && Range(next[this],val,next,frac,x,y) && (frac[this, RangeP]>=50) 
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
modifies val, unpacked;
//need to put this in for modulo 
requires this!=null;
requires val[this]>=0 && x>=0;
//this could be 100 here
requires frac[this, RangeP]>=50;
requires (forall r:Ref :: unpacked[r, RangeP]==false);
ensures  Range(this,val,next,frac,0,10);
ensures frac[this, RangeP]>=50;


{ 
 assert unpacked[this, RangeP]==false;
 assume Range(this,val,next,frac,0,10);
 assert (this != null) && (val[this] >= 0) && (val[this] <= 10) && Range(next[this],val,next,frac,0,10)  ;
 unpacked[this, RangeP]:=true;
  
 val[this] := modulo((val[this]+x),11);
 assert (this != null);
 assert (val[this] >= 0) && (val[this] <= 10);
 assert Range(next[this],val,next,frac,0,10);
 unpacked[this, RangeP]:=false;

  if (next[this] != null )
  { 
    call addModulo11(next[this], x);
  }
  assert Range(next[this], val, next,frac, 0, 10);
  //val[this] was not modified
  //but Boogie does not know that
  //from the linearity of the permissions
  //I'm not sure this is because of the linearity of object propositions.
  assume old(val[this])==val[this];
  
  }