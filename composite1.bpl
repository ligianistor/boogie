//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;

const null: Ref;
const unique leftP: PredicateTypes;
const unique rightP: PredicateTypes;
const unique parentP: PredicateTypes;
const unique countP: PredicateTypes;

var left: [Ref]Ref;
var right: [Ref]Ref;
var parent: [Ref]Ref;
var count: [Ref]int;
var packed: PackedType;
var frac: FractionType;

var lcLeftPred : [Ref]int;
var rcRightPred : [Ref]int;
var cCountPred : [Ref]int;


//axiom that shows there are no cycles in the tree, locally
//this axiom describes the data structure, does not depend on whether 
//a predicate holds or not
axiom (forall this: Ref, l:Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=right[this]) && (this!=left[this]) && (this!=parent[this]));

//axiom stating that this is a binary tree
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=null) && (parent[this]!=null) ==>((this==right[parent[this]]) || (this==left[parent[this]]))
);

procedure PackLeft(this:Ref, lc:int);
ensures ((  (left[this] != null) && 
       packed[left[this], countP] &&
       (cCountPred[left[this]] == lc) &&
       (frac[left[this], countP] >= 50) ) 
                      ==> ( packed[this, leftP] && (lcLeftPred[this] == lc) ) )
  &&
  ( ( (left[this] == null) && (lc==0) ) ==> ( packed[this, leftP] && (lcLeftPred[this] == 0) ) );

procedure UnpackLeftNull(this:Ref, lc:int);
ensures (packed[this, leftP] && (lcLeftPred[this] == 0) ==> (left[this] == null) );

procedure UnpackLeftNotNull(this:Ref, lc:int);
ensures ( (packed[this, leftP] && (lcLeftPred[this] == lc) && (left[this] != null) )
   ==> 
  (  packed[left[this], countP] &&
       (cCountPred[left[this]] == lc)
     && (frac[left[this], countP] >= 50) ) );


procedure PackRight(this:Ref, rc:int);
ensures  ((  (right[this] != null) && 
   packed[right[this], countP] &&
   (cCountPred[right[this]] == rc) &&
 (frac[right[this], countP] >= 50) ) 
                       ==> 
(packed[this, rightP] && (rcRightPred[this] == rc)))
  &&
  ((  (right[this] == null) && (rc==0) ) ==> 
packed[this, rightP] && (rcRightPred[this] == 0)
);

procedure UnpackRightNull(this:Ref, rc:int);
ensures (packed[this, rightP] && (rcRightPred[this] == 0) ==> (right[this] == null) );

procedure UnpackRightNotNull(this:Ref, rc:int);
ensures (packed[this, rightP] && (rcRightPred[this] == rc) && (right[this] != null) ==> 
 ( packed[right[this], countP] && (cCountPred[right[this]] == rc) && (frac[right[this], countP] >= 50) ));

procedure PackCount(this:Ref, c:int);
ensures  ( ( (this!=null) && (
  exists lc: int, rc:int ::
  ( packed[this, leftP] && (lcLeftPred[this] == lc) && 
  (frac[this, leftP] >= 50) &&
  packed[this, rightP] &&
  (rcRightPred[this] == rc) &&
(frac[this, rightP] >= 50) && 
 (count[this] == lc+rc+1) &&
 ( count[this]== c) )
) ) ==> 
packed[this, countP] &&
(cCountPred[this] == c)
);

procedure UnpackCount(this:Ref, c:int);
ensures ( (packed[this, countP] && 
  cCountPred[this] == c
) ==>
    ( (this!=null) && (
  exists lc: int, rc:int ::
  (
packed[this, leftP] &&
(lcLeftPred[this] == lc) &&
 (frac[this, leftP] >= 50) &&
 packed[this, rightP] &&
(rcRightPred[this] == rc) &&
 (frac[this, rightP] >= 50) && 
 (count[this] == lc+rc+1) &&
 ( count[this]== c) )
) ) );



//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref);
ensures   (
    (parent[this] != this) &&
    packed[this, countP] &&
    (cCountPred[this] == count[this]) &&
     (frac[this, countP]>=50) &&
     (parent[this] != null) &&
     packed[parent[this], parentP] &&
            (
           ( packed[parent[this], leftP] &&
             (lcLeftPred[parent[this]]== count[this]) &&
            (frac[parent[this], leftP] >= 50))
             ||
           ( packed[parent[this], rightP] &&
             rcRightPred[parent[this]] ==count[this] &&
            (frac[parent[this], rightP] >= 50))
           ))  
  ==>
  packed[this, parentP];

procedure PackParentNull(this:Ref);
ensures (
  (parent[this] != this) &&
   packed[this, countP] &&
   cCountPred[this] == count[this] &&
   (frac[this, countP]>=100) &&
   (parent[this]==null)
  )
  ==>
    packed[this, parentP];

procedure UnpackParent(this:Ref);
ensures ( packed[this, parentP] ==>
  ( (parent[this] != this)
       &&    
   ( exists c:int::     
     (( packed[this,countP] &&
        (cCountPred[this] == c) &&
     (frac[this, countP]>=50)
     &&
     ((parent[this] != null) ==>
            (packed[parent[this], parentP] &&
            (( packed[parent[this], leftP] && (lcLeftPred[parent[this]]==c) && (frac[parent[this], leftP] >= 50))
             ||
           ( packed[parent[this], rightP] && (rcRightPred[parent[this]]==c)  && (frac[parent[this], rightP] >= 50))
           ) ) )
     &&
     ((parent[this]==null) ==> packed[this,countP] && (cCountPred[this] == c) && (frac[this,countP]>=50) )  ) ))
  )  );


//axioms about the existance of a variable 
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  cCountPred : [Ref]int, 
        lcLeftPred : [Ref]int, packed: PackedType, frac: FractionType::
    (exists lc:int :: packed[this, leftP] && (lcLeftPred[this] == lc)  ==> packed[this, leftP] && (lcLeftPred[this] == count[left[this]])) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, 
       rcRightPred : [Ref]int, packed: PackedType, frac: FractionType::
    (exists rc:int :: packed[this, rightP] && (rcRightPred[this] == rc)  ==> packed[this, rightP] && (rcRightPred[this] == count[right[this]])) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref,  cCountPred : [Ref]int, 
       count: [Ref]int, packed: PackedType, frac: FractionType::
    (exists c:int :: packed[this, countP] && (cCountPred[this] == c)  ==> ( packed[this, countP] && (cCountPred[this] == count[this]) ) )
);


procedure Composite(this:Ref)
modifies left, right, parent, count, frac, packed;
requires this != null;
ensures packed[this, parentP];
ensures packed[this, leftP] && (lcLeftPred[this] == 0);
ensures packed[this, rightP] && (rcRightPred[this] == 0);
ensures (frac[this, parentP] >= 50) && (frac[this, leftP] >= 50) && (frac[this, rightP] >= 50) ;
ensures packed[this, parentP];
{
  count[this] := 1;
  left[this] := null;
  right[this] := null;
  parent[this] := null;

  frac[this, leftP] := 100;

  frac[this, rightP] :=100;

  frac[this, countP] := 100;

  frac[this, parentP] := 100;
  packed[this, parentP]:=true;
}

procedure updateCountRec(this: Ref)
modifies count, frac, packed;
requires this!=null;
requires packed[this, parentP] == false;
requires parent[this]!=null ==> (frac[parent[this], parentP]>0);
requires (parent[this]!=null) && (this==right[parent[this]]) ==> (frac[parent[this], rightP]>=50);
requires (parent[this]!=null) && (this==left[parent[this]]) ==> (frac[parent[this], leftP]>=50);
requires parent[this]==null ==> (frac[this, countP] >= 50);
requires (forall r:Ref:: (r!=this) ==> packed[r, countP]);
requires packed[this, leftP];
requires packed[this, rightP];
requires (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50);
requires (frac[this, countP] >= 50);

ensures   (packed[this, parentP]);    

{
 var fracLocal: FractionType;

  if (parent[this] != null)
 {

//we assert what is true when packed[this, parentP]==false
assert frac[this, countP]>=50;
fracLocal[this, countP]:=frac[this, countP];

//this asserts that we have a fraction to parentP
assert (frac[parent[this], parentP]>0);
//we unpack parent[this] from parentP
//might need to say that other objects are not unpacked for parentP
packed[parent[this], parentP]:=false;
assert (forall r:Ref:: (r!=this) ==> (packed[r, countP]));

//we can assume this because we just unpacked
//parent[this] from parentP
assume frac[parent[this], countP]>=50;
fracLocal[parent[this], countP]:=frac[parent[this], countP];


//we unpack parent[this] from countP
packed[parent[this], countP]:=false;

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
packed[parent[this], rightP]:=false;
assert  (packed[parent[this],rightP]==false)  ==> frac[right[parent[this]],countP]>=50;
fracLocal[this, countP]:=fracLocal[this, countP]+frac[this, countP];

assert (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50);
assert packed[this, parentP]==false;
frac[this, countP]:=fracLocal[this, countP];
assert (frac[this, countP] >= 100);
assert packed[this, rightP] && (rcRightPred[this] == count[right[this]]);
assert (exists c2:int :: packed[this, rightP] && (rcRightPred[this] == c2));
packed[this, rightP]:=true;
assert packed[this, leftP] && (lcLeftPred[this] == count[left[this]]);
assert (exists c1:int :: packed[this, leftP] && (lcLeftPred[this] == c1)); 
packed[this, leftP]:=true;
      call updateCount(this);
assert (exists c:int ::
          packed[this, countP] && (cCountPred[this] == c)
         );
assert packed[this, countP] && (cCountPred[this] == count[this]);
assert packed[this, countP];
assert (frac[this, countP]>=100)  ; 

//assert the preconditions of updateCountRec
assert parent[this]!=null;
packed[parent[this], parentP]:=false;

//we can assume these because we have just unpacked parent[this] from parentP
assume parent[parent[this]]!=null ==> ( frac[parent[parent[this]], parentP]>0);
assume parent[parent[this]]==null ==> (frac[parent[this], countP] >= 50);
assume (parent[parent[this]]!=null) && (this==right[parent[parent[this]]]) ==> (frac[parent[parent[this]], rightP]>=50);
assume (parent[parent[this]]!=null) && (this==left[parent[parent[this]]]) ==> (frac[parent[parent[this]], leftP]>=50);


assert packed[parent[this], rightP] && (rcRightPred[parent[this]] == count[this]);
assert (exists c2:int :: packed[parent[this], rightP] && (rcRightPred[parent[this]] == c2));
packed[parent[this],rightP]:=true;
assert (forall r:Ref:: (r!=parent[this]) ==> (packed[r, countP]));

//assertions for proving isPackedLeftPred(parent[this]...
//we assume this, the other case is trivial
//we could write a new procedure for the other case?
assume left[parent[this]] != null;
assert packed[left[parent[this]], countP];
//we can assume this because isPackedCountPred is packed for left[parent[this]]
assume packed[left[parent[this]], countP] && (cCountPred[left[parent[this]]]==count[this]);

assert packed[parent[this], leftP] && (lcLeftPred[parent[this]]== count[left[parent[this]]]);
assert (exists c1:int :: packed[parent[this], leftP] && (lcLeftPred[parent[this]]== c1)); 
packed[parent[this],leftP]:=true;
      call updateCountRec(parent[this]);
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

  }  
 }


 
 procedure updateCount(this: Ref)
 modifies count, frac, packed;
 requires this != null;
 requires packed[this, leftP];
 requires packed[this, rightP];
 requires (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50)  && (frac[this, countP] >= 100);
        
ensures ( exists c:int :: packed[this, countP] && (cCountPred[this]==c)
         );
ensures packed[this, countP];
ensures (frac[this, countP]>=100);
ensures (forall r:Ref:: (r!=this) ==> (packed[r, countP]==old(packed[r, countP])));
     

 {
   var newc:int;
   newc := 1;


        if (left[this] != null)
           {
       newc := newc + count[left[this]];
       }
       
        if (right[this] != null)
             {
         
         newc := newc + count[right[this]];
         
       }
        
    count[this] := newc;   
       
 
    packed[this, countP]:=true;
    
      }


procedure setLeft(this: Ref, l:Ref)
modifies parent, left, count, frac, packed;
requires this!=null;
requires this!=l;
requires l!=null;
requires packed[this, parentP];
requires packed[l, parentP];
requires (forall r:Ref:: packed[r, countP]);
ensures packed[this, parentP];
 {

packed[this, parentP]:=false;


   parent[l]:=this;
   left[this]:=l;


packed[this, leftP]:=true;

packed[this, rightP]:=true;

packed[this, countP]:=false;


   call updateCountRec(this);
   
}
