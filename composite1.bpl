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

procedure PackLeftNotNull(this:Ref, lc:int);
requires (left[this] != null) && 
       packed[left[this], countP] &&
       (cCountPred[left[this]] == lc) &&
       (frac[left[this], countP] >= 50);  
ensures (lcLeftPred[this] == lc);


procedure PackLeftNull(this:Ref, lc:int);
requires (left[this] == null) && (lc==0);
ensures (lcLeftPred[this] == 0);

procedure UnpackLeftNull(this:Ref, lc:int);
requires packed[this, leftP] && (lcLeftPred[this] == 0);
ensures left[this] == null;

procedure UnpackLeftNotNull(this:Ref, lc:int);
requires packed[this, leftP] && (lcLeftPred[this] == lc) && (left[this] != null);
ensures  packed[left[this], countP] &&
       (cCountPred[left[this]] == lc)
     && (frac[left[this], countP] >= 50);


procedure PackRightNotNull(this:Ref, rc:int);
requires  (right[this] != null) && 
   packed[right[this], countP] &&
   (cCountPred[right[this]] == rc) &&
 (frac[right[this], countP] >= 50) ;
ensures (rcRightPred[this] == rc);

procedure PackRightNull(this:Ref, rc:int);
requires   (right[this] == null) && (rc==0);
ensures (rcRightPred[this] == 0);

procedure UnpackRightNull(this:Ref, rc:int);
requires packed[this, rightP] && (rcRightPred[this] == 0);
ensures right[this] == null;

procedure UnpackRightNotNull(this:Ref, rc:int);
requires packed[this, rightP] && (rcRightPred[this] == rc) && (right[this] != null);
ensures  packed[right[this], countP] &&
 (cCountPred[right[this]] == rc) && (frac[right[this], countP] >= 50);

procedure PackCount(this:Ref, c:int);
requires  (this!=null) && (
  ( exists lc: int, rc:int ::
   countPredFunc(this, count,  lc, rc, 
        lcLeftPred, rcRightPred, packed, frac) ) &&
 ( count[this]== c)
);
ensures (cCountPred[this] == c);

procedure UnpackCount(this:Ref, c:int);
requires packed[this, countP] && 
  cCountPred[this] == c;
ensures    (this!=null) && (
  exists lc: int, rc:int ::
  (packed[this, leftP] &&
(lcLeftPred[this] == lc) &&
 (frac[this, leftP] >= 50) &&
 packed[this, rightP] &&
(rcRightPred[this] == rc) &&
 (frac[this, rightP] >= 50) && 
 (count[this] == lc+rc+1) &&
 ( count[this]== c) )
);



//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref);
requires   (parent[this] != this) &&
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
           );

procedure PackParentNull(this:Ref);
requires (parent[this] != this) &&
   packed[this, countP] &&
   cCountPred[this] == count[this] &&
   (frac[this, countP]>=100) &&
   (parent[this]==null);

procedure UnpackParent(this:Ref);
requires packed[this, parentP];
ensures (parent[this] != this)
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
     ((parent[this]==null) ==> packed[this,countP] && (cCountPred[this] == c) && (frac[this,countP]>=50) )  ) ));


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

function countPredFunc(this: Ref, count: [Ref]int,  lc1:int, rc1:int, 
        lcLeftPred : [Ref]int, rcRightPred : [Ref]int, packed: PackedType, frac: FractionType) : bool;

//axiom about existance of variable, but the other way of the implication
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  lc1:int, rc1:int, 
        lcLeftPred : [Ref]int, rcRightPred : [Ref]int, packed: PackedType, frac: FractionType::
    (
(
  ( packed[this, leftP] && (lcLeftPred[this] == lc1) && 
  (frac[this, leftP] >= 50) &&
  packed[this, rightP] &&
  (rcRightPred[this] == rc1) &&
(frac[this, rightP] >= 50) && 
 (count[this] == lc1+rc1+1) )
)
 ==> countPredFunc(this, count,  lc1, rc1, 
        lcLeftPred, rcRightPred, packed, frac)
) 
);


procedure Composite(this:Ref)
modifies left, right, parent, count, frac, packed;
requires this != null;
ensures packed[this, parentP];
ensures packed[this, leftP] && (lcLeftPred[this] == 0);
ensures packed[this, rightP] && (rcRightPred[this] == 0);
ensures (frac[this, parentP] >= 50) && (frac[this, leftP] >= 50) && (frac[this, rightP] >= 50) ;
{

  count[this] := 1;
  left[this] := null;
  right[this] := null;
  parent[this] := null;
call PackLeftNull(this, 0);
packed[this, leftP] := true;
frac[this, leftP] := 100;
call PackRightNull(this,0);
packed[this, rightP] := true;
frac[this, rightP] :=100;

//need to put in the assertions that are related to exists
//Boogie does not know how to intantiate the exists but we know
assert countPredFunc(this, count,  0, 0, 
        lcLeftPred, rcRightPred, packed, frac);

call PackCount(this,1);
packed[this, countP] := true;
 frac[this, countP] := 100;
call PackParentNull(this);
packed[this, parentP] := true;
frac[this, parentP] := 100;
}



 
 procedure updateCount(this: Ref)
 modifies count, frac, packed;
 requires this != null;
 requires packed[this, leftP];
 requires packed[this, rightP];
 requires (frac[this,leftP] >=50) &&   (frac[this,rightP] >=50)  && (frac[this, countP] >= 100);
        
ensures ( exists c:int :: (cCountPred[this]==c));
ensures packed[this, countP];
ensures (frac[this, countP]>=100);
     

 {
   var newc:int;
   newc := 1;


        if (left[this] != null)
           {
 	call UnpackLeftNotNull(this, lcLeftPred[this]);
	packed[this, leftP]:=false;
	call UnpackCount(left[this], cCountPred[left[this]]);
	packed[left[this], countP]:=false; 
        newc := newc + count[left[this]];
	assert countPredFunc(left[this], count,  lcLeftPred[left[this]],  rcRightPred[left[this]], 
        lcLeftPred, rcRightPred, packed, frac);
	call PackCount(left[this], cCountPred[left[this]]);
	packed[left[this], countP]:=true;
       }
       
        if (right[this] != null)
             {
         call UnpackRightNotNull(this, rcRightPred[this]);
	 packed[this, rightP]:=false;
	call UnpackCount(right[this], cCountPred[right[this]]);
         newc := newc + count[right[this]];
         
       }
        
    count[this] := newc;   
       
 
    packed[this, countP]:=true;
    
}
