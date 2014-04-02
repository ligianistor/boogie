//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type UnpackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique leftP: PredicateTypes;
const unique rightP: PredicateTypes;
const unique parentP: PredicateTypes;
const unique countP: PredicateTypes;

var left: [Ref]Ref;
var right: [Ref]Ref;
var parent: [Ref]Ref;
var count: [Ref]int;
var unpacked: UnpackedType;
var frac: FractionType;


//axiom that shows there are no cycles in the tree, locally
//this axiom describes the data structure, does not depend on whether 
//a predicate holds or not
axiom (forall this: Ref, l:Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=right[this]) && (this!=left[this]) && (this!=parent[this]));

//axiom stating that this is a binary tree
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=null) && (parent[this]!=null) ==>((this==right[parent[this]]) || (this==left[parent[this]]))
);

function isPackedLeftPred(this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType, lc: int) returns (bool);
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType,  lc: int::
  ((  (left[this] != null) && isPackedCountPred(left[this],left, right, count, frac, lc) && (frac[left[this], countP] >= 50) ) 
                      ==> (isPackedLeftPred(this, left, right, count, frac, lc) ) )
  &&
  ( ( (left[this] == null) && (lc==0) ) ==> (isPackedLeftPred(this, left, right, count, frac, 0) ) )
);
 
//this axiom is for unpacking of left predicate when left[this]!= null
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref,count: [Ref]int, frac: FractionType,  lc: int::
  ( (isPackedLeftPred(this, left, right, count, frac, lc) && (left[this] != null) )==> 
  ( isPackedCountPred(left[this],left, right, count, frac, lc) && (frac[left[this], countP] >= 50) ) ) ) ;

//this axiom is for unpacking of left predicate when left[this]== null
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType::
  {isPackedLeftPred(this, left, right, count, frac, 0)}
   (isPackedLeftPred(this, left, right,count, frac, 0) ==> (left[this] == null) ) );



function isPackedRightPred(this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType,  rc: int) returns (bool);
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType,  rc: int::
  ((  (right[this] != null) && isPackedCountPred(right[this],left, right, count, frac, rc) && (frac[right[this], countP] >= 50) ) 
                       ==> isPackedRightPred(this, left, right, count, frac, rc)  )
  &&
  ((  (right[this] == null) && (rc==0) ) ==> isPackedRightPred(this, left, right, count, frac, 0) )
);

//this axiom is for unpacking of right predicate when right[this]!=null
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType,  rc: int::
  (isPackedRightPred(this, left, right, count, frac, rc) && (right[this] != null) ==> 
 (isPackedCountPred(right[this],left, right, count, frac, rc) && (frac[right[this], countP] >= 50) )));


//this axiom is for unpacking of right predicate when right[this]==null
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType::
   (isPackedRightPred(this, left, right, count, frac, 0) ==> (right[this] == null) ) );


function isPackedCountPred(this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType, c: int) returns (bool);
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType, c:int ::
 ( ( (this!=null) && (
  exists lc: int, rc:int ::
  (isPackedLeftPred(this, left, right, count, frac, lc) && (frac[this, leftP] >= 50)
  && isPackedRightPred(this, left, right, count, frac, rc) && (frac[this, rightP] >= 50) &&  (count[this] == lc+rc+1) && ( count[this]== c) )
) ) ==> isPackedCountPred(this, left, right, count, frac, c) )
);

//this axiom is used for unpacking of count predicate
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType, c:int ::
 ( isPackedCountPred(this, left, right, count, frac, c) ==>
    ( (this!=null) && (
  exists lc: int, rc:int ::
  (isPackedLeftPred(this, left, right, count, frac, lc) && (frac[this, leftP] >= 50)
  && isPackedRightPred(this, left, right, count, frac, rc) && (frac[this, rightP] >= 50) &&  (count[this] == lc+rc+1) && ( count[this]== c) )
) ) )
);



axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

function isPackedParentPred(this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent: [Ref]Ref, count: [Ref]int, frac: FractionType) returns (bool);
axiom ( forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent: [Ref]Ref, count: [Ref]int, frac: FractionType ::
  (
    (parent[this] != this)
     &&
     isPackedCountPred(this, left, right, count, frac, count[this])
     &&
     (frac[this, countP]>=50)
     &&
     (parent[this] != null) 
     &&
     isPackedParentPred(parent[this], left, right, parent, count, frac)
     &&
            (
           (isPackedLeftPred(parent[this], left, right, count, frac, count[this]) && (frac[parent[this], leftP] >= 50))
             ||
           (isPackedRightPred(parent[this], left, right, count, frac, count[this]) && (frac[parent[this], rightP] >= 50))
           )

  )  
  ==>
  isPackedParentPred(this, left, right, parent, count, frac) 
);



axiom ( forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent: [Ref]Ref, count: [Ref]int, frac: FractionType ::
  (
  (parent[this] != this)
   &&
   isPackedCountPred(this, left, right, count, frac, count[this])
   &&
   (frac[this, countP]>=100)
   &&
   (parent[this]==null)
  )
  ==>
  isPackedParentPred(this, left, right, parent, count, frac)
);

//this axiom is used for unpacking of isPackedParentPred
axiom ( forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent: [Ref]Ref, count: [Ref]int, frac: FractionType ::
  {isPackedParentPred(this, left, right, parent, count, frac)}
  ( isPackedParentPred(this, left, right, parent, count, frac) ==>
  ( (parent[this] != this)
       &&    
   ( exists c:int::     
     ((isPackedCountPred(this, left, right, count, frac, c)
     &&
     (frac[this, countP]>=50)
     &&
     ((parent[this] != null) ==>
            (isPackedParentPred(parent[this], left, right, parent, count, frac)
             &&
            ((isPackedLeftPred(parent[this], left, right, count, frac, c) && (frac[parent[this], leftP] >= 50))
             ||
           (isPackedRightPred(parent[this], left, right, count, frac, c) && (frac[parent[this], rightP] >= 50))
           ) ) )
     &&
     ((parent[this]==null) ==> isPackedCountPred(this, left, right, count, frac, c) && (frac[this,countP]>=50) )  ) ))
  )  ) );

//these axioms are for when a predicate is unpacked the first time
//axioms for when the predicate parentP is unpacked
//axiom ( forall this:Ref, parent: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//unpacked[this,parentP] ==> (frac[this, countP]>=50));

//axiom ( forall this:Ref, parent: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//unpacked[this,parentP]  ==> ((parent[this]!=null)==> (frac[parent[this], parentP]>0)));


//axiom ( forall this:Ref, parent: [Ref]Ref, right:[Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//(unpacked[this,parentP] ==>((parent[this]!=null) && (this==right[parent[this]])) ==>
//                                      frac[parent[this],rightP]>=50)) ;


//axiom ( forall this:Ref, parent: [Ref]Ref, left: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//(unpacked[this,parentP] ==> ((parent[this]!=null) && (this==left[parent[this]])) ==>
//                                      frac[parent[this], leftP]>=50) );

//axiom ( forall this:Ref, parent: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//(unpacked[this,parentP] ==> ((parent[this]==null))==> (frac[this, countP]>=50) ));

//axioms for when the predicate countP is unpacked
//axiom ( forall this:Ref, frac: FractionType, unpacked: UnpackedType  ::
//   unpacked[this,countP] ==> (frac[this,leftP]>=50) && 
//                              (frac[this,rightP]>=50 )) ;


//axioms for when the predicate leftP is unpacked
//axiom ( forall this:Ref, left: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//   unpacked[this,leftP] ==> frac[left[this],countP]>=50 );


 //axioms for when the predicate rightP is unpacked
//axiom ( forall this:Ref, right: [Ref]Ref, frac: FractionType, unpacked: UnpackedType  ::
//   unpacked[this,rightP]  ==> frac[right[this],countP]>=50 );


//axioms about the existance of a variable 
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType::
    (exists lc:int :: isPackedLeftPred(this, left, right, count, frac, lc)  ==> isPackedLeftPred(this, left, right, count, frac, count[left[this]])) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType::
    (exists rc:int :: isPackedRightPred(this, left, right, count, frac, rc)  ==> isPackedRightPred(this, left, right, count, frac, count[right[this]])) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, frac: FractionType::
    (exists c:int :: isPackedCountPred(this, left, right, count, frac, c)  ==> (isPackedCountPred(this, left, right, count, frac, count[this])) )
);

//sort of frame axiom for count and isPackedLeftPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  count1: [Ref]int, frac: FractionType,  lc: int::
 (isPackedLeftPred(this, left, right, count, frac, lc) && (count1[left[this]]==count[left[this]]) ==> isPackedLeftPred(this, left, right, count1, frac, lc))
 );


//a kind of frame axiom for isPackedRightPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  left1: [Ref]Ref, frac: FractionType,  rc: int::
 (isPackedRightPred(this, left, right, count, frac, rc) && ((left1[this]!=left[this])||(left1[this]==left[this])) ==> isPackedRightPred(this, left1, right, count, frac, rc))
 );

//kind of frame axioms for when frac is modified, for isPackedRightPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  frac: FractionType, frac1: FractionType, rc:int::
 (isPackedRightPred(this, left, right, count, frac, rc) && 
     (forall r:Ref, p:PredicateTypes:: (frac1[r,p]==frac[r,p]) || (frac1[r,p]!=frac[r,p])) ==> 
  (isPackedRightPred(this, left, right, count, frac1, rc)))
 );

//kind of frame axioms for when frac is modified, for isPackedLeftPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  frac: FractionType, frac1: FractionType, lc:int::
 (isPackedLeftPred(this, left, right, count, frac, lc) && 
     (forall r:Ref, p:PredicateTypes:: (frac1[r,p]==frac[r,p]) || (frac1[r,p]!=frac[r,p])) ==> 
  (isPackedLeftPred(this, left, right, count, frac1, lc)))
 );


//sort of frame axiom for count and isPackedRightPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  count1: [Ref]int, frac: FractionType,  rc: int::
 (isPackedRightPred(this, left, right, count, frac, rc) && (count1[right[this]]==count[right[this]]) ==> isPackedRightPred(this, left, right, count1, frac, rc))
 );


//frame axiom for isPackedCountPred
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent: [Ref]Ref, count: [Ref]int,  left1: [Ref]Ref, frac: FractionType,  c: int::
 (isPackedCountPred(this, left, right, count, frac, c) && (left1[parent[this]]==this)  ==> isPackedCountPred(this, left1, right, count, frac, c))
 );


procedure Composite(this:Ref)
modifies left, right, parent, count, frac, unpacked;
requires this != null;
ensures isPackedParentPred(this, left, right, parent, count, frac);
ensures isPackedLeftPred(this, left, right, count, frac, 0);
ensures isPackedRightPred(this, left, right, count, frac, 0);
ensures (frac[this, parentP] >= 50) && (frac[this, leftP] >= 50) && (frac[this, rightP] >= 50) ;
ensures unpacked[this, parentP]==false;
{
  count[this] := 1;
  left[this] := null;
  right[this] := null;
  parent[this] := null;
  assert isPackedLeftPred(this, left, right, count, frac, 0);
  frac[this, leftP] := 100;
  assert isPackedRightPred(this, left, right, count, frac, 0);
  frac[this, rightP] :=100;
  assert isPackedLeftPred(this, left, right, count, frac, 0) && isPackedRightPred(this, left, right, count, frac, 0) ;
  assert isPackedCountPred(this, left, right, count, frac, 1);
  frac[this, countP] := 100;
  assert isPackedLeftPred(this, left, right, count, frac, 0) && isPackedRightPred(this, left, right, count, frac, 0) ;
  assert isPackedCountPred(this, left, right, count, frac, 1);
  assert isPackedParentPred(this, left, right, parent, count, frac);
  frac[this, parentP] := 100;
  assert isPackedLeftPred(this, left, right, count, frac, 0) && isPackedRightPred(this, left, right,count, frac, 0) ;
  assert isPackedCountPred(this, left, right, count, frac, 1);
  assert isPackedParentPred(this, left, right, parent, count, frac);
  unpacked[this, parentP]:=false;
}

procedure updateCountRec(this: Ref)
modifies count, frac, unpacked;
requires this!=null;
requires unpacked[this, parentP];
requires parent[this]!=null ==> (frac[parent[this], parentP]>0);
requires (parent[this]!=null) && (this==right[parent[this]]) ==> (frac[parent[this], rightP]>=50);
requires (parent[this]!=null) && (this==left[parent[this]]) ==> (frac[parent[this], leftP]>=50);
requires parent[this]==null ==> (frac[this, countP] >= 50);
requires (forall r:Ref:: (r!=this) ==> (unpacked[r, countP]==false));
requires unpacked[this, leftP]==false;
requires unpacked[this, rightP]==false;
requires (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50);
requires (frac[this, countP] >= 50);

ensures   (isPackedParentPred(this, left, right, parent, count, frac) );    

{
 var fracLocal: FractionType;

assume (exists c1:int :: isPackedLeftPred(this, left, right, count, frac, c1)); 
assume (exists c2:int :: isPackedRightPred(this, left, right, count, frac, c2));

  if (parent[this] != null)
 {

//we assert what is true when unpacked[this, parentP]
assert frac[this, countP]>=50;
fracLocal[this, countP]:=frac[this, countP];

//this asserts that we have a fraction to parentP
assert (frac[parent[this], parentP]>0);
//we unpack parent[this] from parentP
//might need to say that other objects are not unpacked for parentP
unpacked[parent[this], parentP]:=true;
assert (forall r:Ref:: (r!=this) ==> (unpacked[r, countP]==false));

//we can assume this because we just unpacked
//parent[this] from parentP
assume frac[parent[this], countP]>=50;
fracLocal[parent[this], countP]:=frac[parent[this], countP];


//we unpack parent[this] from countP
unpacked[parent[this], countP]:=true;

//we can assume this because we just unpacked parent[this] from countP
assume (frac[this,leftP]>=50) && (frac[this,rightP]>=50);
fracLocal[parent[this], rightP]:=frac[parent[this], rightP];


//we assume this is the right child of parent[this]
//the other case is analogous
assume this==right[parent[this]];
assert (parent[this]!=null) && (this==right[parent[this]]) ==> frac[parent[this],rightP]>=50;
fracLocal[parent[this],rightP]:=fracLocal[parent[this], rightP] +frac[parent[this],rightP];

assert (fracLocal[parent[this],rightP]>=100);
//unpack parent[this] from rightP
unpacked[parent[this], rightP]:=true;
assert  unpacked[parent[this],rightP]  ==> frac[right[parent[this]],countP]>=50;
fracLocal[this, countP]:=fracLocal[this, countP]+frac[this, countP];

assert (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50);
assert unpacked[this, parentP];
frac[this, countP]:=fracLocal[this, countP];
assert (frac[this, countP] >= 100);
assert isPackedRightPred(this, left, right, count, frac, count[right[this]]);
assert (exists c2:int :: isPackedRightPred(this, left, right, count, frac, c2));
unpacked[this, rightP]:=false;
assert isPackedLeftPred(this, left, right, count, frac, count[left[this]]);
assert (exists c1:int :: isPackedLeftPred(this, left, right, count, frac, c1)); 
unpacked[this, leftP]:=false;
      call updateCount(this);
assert( exists c:int ::
          isPackedCountPred(this, left, right, count, frac, c)
         );
assert isPackedCountPred(this, left, right, count, frac, count[this]);
assert unpacked[this, countP]==false;
assert (frac[this, countP]>=100)  ; 

//assert the preconditions of updateCountRec
assert parent[this]!=null;
unpacked[parent[this], parentP]:=true;

//we can assume these because we have just unpacked parent[this] from parentP
assume parent[parent[this]]!=null ==> ( frac[parent[parent[this]], parentP]>0);
assume parent[parent[this]]==null ==> (frac[parent[this], countP] >= 50);
assume (parent[parent[this]]!=null) && (this==right[parent[parent[this]]]) ==> (frac[parent[parent[this]], rightP]>=50);
assume (parent[parent[this]]!=null) && (this==left[parent[parent[this]]]) ==> (frac[parent[parent[this]], leftP]>=50);


assert isPackedRightPred(parent[this], left, right, count, frac, count[this]);
assert (exists c2:int :: isPackedRightPred(parent[this], left, right, count, frac, c2));
unpacked[parent[this],rightP]:=false;
assert (forall r:Ref:: (r!=parent[this]) ==> (unpacked[r, countP]==false));

//assertions for proving isPackedLeftPred(parent[this]...
//we assume this, the other case is trivial
//we could write a new procedure for the other case?
assume left[parent[this]] != null;
assert unpacked[left[parent[this]], countP]==false;
//we can assume this because isPackedCountPred is packed for left[parent[this]]
assume isPackedCountPred(left[parent[this]],left, right, count, frac, count[this]);

assert isPackedLeftPred(parent[this], left, right, count, frac, count[left[parent[this]]]);
assert (exists c1:int :: isPackedLeftPred(parent[this], left, right, count, frac, c1)); 
unpacked[parent[this],leftP]:=false;


      call updateCountRec(parent[this]);
assert isPackedParentPred(parent[this], left, right, parent, count, frac);

//this is the final assertion needed          
assert isPackedParentPred(this, left, right, parent, count, frac);
      }
    else
  { 
assert (frac[this, countP] >= 50);
fracLocal[this, countP]:=frac[this, countP];
assert  parent[this]==null ==> (frac[this, countP] >= 50);
fracLocal[this, countP]:=fracLocal[this, countP] + frac[this, countP];
frac[this, countP]:=fracLocal[this, countP];
assert (frac[this, countP] >= 100);    
 
         call updateCount(this);

assert isPackedParentPred(this, left, right, parent, count, frac);
  }  
 }


 
 procedure updateCount(this: Ref)
 modifies count, frac, unpacked;
 requires this != null;
 requires unpacked[this, leftP]==false;
 requires unpacked[this, rightP]==false;
 requires (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50)  && (frac[this, countP] >= 100);
        
ensures ( exists c:int ::
          isPackedCountPred(this, left, right, count, frac, c)
         );
ensures unpacked[this, countP]==false;
ensures (frac[this, countP]>=100);
ensures (forall r:Ref:: (r!=this) ==> (unpacked[r, countP]==old(unpacked[r, countP])));
     

 {
   var newc:int;
   newc := 1;

   //we can assume this because leftP and rightP are unpacked
   assume (exists c1:int :: isPackedLeftPred(this, left, right, count, frac, c1));
   assume (exists c2:int :: isPackedRightPred(this, left, right, count, frac, c2));
     
   assert isPackedLeftPred(this, left, right, count, frac, count[left[this]]);
   assert isPackedRightPred(this, left, right, count, frac, count[right[this]]);

        if (left[this] != null)
           {
       newc := newc + count[left[this]];
       }
       
        if (right[this] != null)
             {
         
         newc := newc + count[right[this]];
         
       }
        
    count[this] := newc;   
       
    assert isPackedLeftPred(this, left, right, count, frac, count[left[this]]);
    assert isPackedRightPred(this, left, right, count, frac,  count[right[this]]);
    assert (newc==1+count[left[this]]+ count[right[this]]);
    assert (count[this]==1+count[left[this]]+ count[right[this]]);
    assert (frac[this, leftP] >= 50) ;
    assert (frac[this, rightP] >= 50);
    assert count[this]==newc;
    assert this!=null;
    assert isPackedCountPred(this,left, right, count, frac, newc);
    unpacked[this, countP]:=false;
    
      }


procedure setLeft(this: Ref, l:Ref)
modifies parent, left, count, frac, unpacked;
requires this!=null;
requires this!=l;
requires l!=null;
requires unpacked[this, parentP]==false;
requires unpacked[l, parentP]==false;
requires (forall r:Ref:: (unpacked[r, countP]==false));
ensures isPackedParentPred(this, left, right, parent, count, frac); 
 {
//we can assume these becase isPackedParentPred is true for this and l
assume isPackedParentPred(this, left, right, parent, count, frac);
assume isPackedParentPred(l,left, right, parent, count, frac);

unpacked[this, parentP]:=true;
//we can assume the following because we have just unpacked this from parentP
assume parent[this]!=null ==> (frac[parent[this], parentP]>0);
assume (parent[this]!=null) && (this==right[parent[this]]) ==> (frac[parent[this], rightP]>=50);
assume (parent[this]!=null) && (this==left[parent[this]]) ==> (frac[parent[this], leftP]>=50);
assume parent[this]==null ==> (frac[this, countP] >= 50);

assert (exists c: int :: isPackedRightPred(this, left, right, count, frac, c) );
assert isPackedRightPred(this, left, right, count, frac, count[right[this]]) ;
assert (exists c: int :: isPackedCountPred(l, left, right, count, frac, c) );
assert isPackedCountPred(l, left, right, count, frac, count[l]);

   parent[l]:=this;
   left[this]:=l;
assert this==parent[l];
//proving the assertions for updateCountRec
assert this!=null;
assert  unpacked[this, parentP]; 

assert left[this] != null;
assert isPackedCountPred(left[this], left, right, count, frac, count[left[this]]);
assert frac[left[this], countP] >= 50;
assert isPackedLeftPred(this, left, right, count, frac, count[left[this]]);
unpacked[this, leftP]:=false;

assert isPackedRightPred(this, left, right, count, frac, count[right[this]]) ;
assert (exists c2:int :: isPackedRightPred(this, left, right, count, frac, c2)); 
unpacked[this, rightP]:=false;

assert (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50);
assert (frac[this, countP] >= 50);
unpacked[this, countP]:=true;
assert (forall r:Ref:: (r!=this) ==> (unpacked[r, countP]==false));


assert this!=null;
assert unpacked[this, parentP];

   call updateCountRec(this);
   
}
