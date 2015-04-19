type Ref;

const null: Ref;

var left : [Ref]Ref;
var right : [Ref]Ref;
var parent : [Ref]Ref;
var count : [Ref]int;

var packedCount : [Ref, int] bool;
var packedLeft : [Ref, int] bool;
var packedRight : [Ref, int] bool;
var packedParent : [Ref] bool;

var fracCount : [Ref, int] real;
var fracLeft : [Ref, int] real;
var fracRight : [Ref, int] real;
var fracParent : [Ref] real;

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
requires (packedLeft[this, lc] == false) &&
	 (left[this] != null) && 
       packedCount[left[this], lc] &&
       (fracCount[left[this], lc] >= 0.5);  

procedure PackLeftNull(this:Ref, lc:int);
requires (packedLeft[this, 0] == false) &&
	 (left[this] == null);

procedure UnpackLeftNull(this:Ref, lc:int);
requires packedLeft[this, 0] && 
	(fracLeft[this, 0] > 0.0);
ensures (left[this] == null);

procedure UnpackLeftNotNull(this:Ref, lc:int);
requires packedLeft[this, lc] && 
	 (fracLeft[this, lc] > 0.0) && 
	 (left[this] != null);
ensures  packedCount[left[this], lc] &&
         (fracCount[left[this], lc] >= 0.5);

procedure PackRightNotNull(this:Ref, rc:int);
requires (packedRight[this, rc] == false) &&
	 (right[this] != null) && 
	 packedCount[right[this], rc] &&
         (fracCount[right[this], rc] >= 0.5) ;

procedure PackRightNull(this:Ref, rc:int);
requires (packedRight[this, 0] == false) &&
	 (right[this] == null);

procedure UnpackRightNull(this:Ref, rc:int);
requires packedRight[this, 0] && (fracRight[this, 0] > 0.0);
ensures right[this] == null;

procedure UnpackRightNotNull(this:Ref, rc:int);
requires packedRight[this, rc] && 
	(fracRight[this, rc] > 0.0) && 
	(right[this] != null);
ensures  packedCount[right[this], rc] &&
        (fracCount[right[this], rc] >= 0.5);

procedure PackCount(this:Ref, c:int);
requires (packedCount[this, c] == false) &&
	 (this!=null) && (
  ( exists lc: int, rc:int ::
   countPredFunc(this, count,  lc, rc, 
   packedLeft, fracLeft, packedRight, fracRight) ) 
);

procedure UnpackCount(this:Ref, c:int);
requires packedCount[this, c] && 
	(fracCount[this, c] > 0.0);
ensures (this!=null) && (
  exists lc: int, rc:int ::
  (packedLeft[this, lc] &&
 (fracLeft[this, lc] >= 0.5) &&
 packedRight[this, rc] &&
 (fracRight[this, rc] >= 0.5) && 
 (count[this] == lc+rc+1))
);


//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref);
requires (packedParent[this] == false) &&
	(parent[this] != this) &&
	packedCount[this, count[this]] &&
     (fracCount[this, count[this]] >= 0.5) &&
     (parent[this] != null) &&
     packedParent[parent[this]] &&
            (
           ( packedLeft[parent[this], count[this]] &&
            (fracLeft[parent[this], count[this]] >= 0.5))
             ||
           ( packedRight[parent[this], count[this]] &&
            (fracRight[parent[this], count[this]] >= 0.5))
           );

procedure PackParentNull(this:Ref);
requires (packedParent[this] == false) &&
	(parent[this] != this) &&
        packedCount[this, count[this]] &&
   (fracCount[this, count[this]] == 1.0) &&
   (parent[this]==null);

procedure UnpackParent(this:Ref);
requires packedParent[this] &&
	(fracParent[this] > 0.0);
ensures (parent[this] != this)
       &&    
   ( exists c:int::     
     (( packedCount[this,c] &&
     (fracCount[this, c] >= 0.5)
     &&
     ((parent[this] != null) ==>
            (packedParent[parent[this]] &&
            (( packedLeft[parent[this], c] && (fracLeft[parent[this], c] >= 0.5))
             ||
           ( packedRight[parent[this], c] && (fracRight[parent[this], c] >= 0.5))
           ) ) )
     &&
     ((parent[this]==null) ==> packedCount[this, c] && (fracCount[this,c] >= 0.5) )  ) ));


//axioms about the existance of a variable 
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  
        packedLeft: [Ref, int]bool, fracLeft: [Ref, int]real ::
    (exists lc:int :: packedLeft[this, lc] ==> packedLeft[this, count[left[this]]]) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int, 
       packedRight: [Ref, int]bool, fracRight: [Ref, int]real ::
    (exists rc:int :: packedRight[this, rc] ==> packedRight[this, count[right[this]]]) 
);

axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, 
       count: [Ref]int, packedCount: [Ref, int]bool, fracCount: [Ref, int]real::
    (exists c:int :: packedCount[this, c] ==> (packedCount[this, count[this]]) )
);

function countPredFunc(this: Ref, count: [Ref]int,  lc1:int, rc1:int, 
         packedLeft: [Ref, int]bool, fracLeft: [Ref, int]real, 
	 packedRight: [Ref, int]bool, fracRight: [Ref, int]real) : bool;

//axiom about existance of variable, but the other way of the implication
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, count: [Ref]int,  lc1:int, rc1:int, 
      packedLeft: [Ref, int]bool, fracLeft: [Ref, int]real, 
      packedRight: [Ref, int]bool, fracRight: [Ref, int]real ::
    (
(
  ( packedLeft[this, lc1] && 
  (fracLeft[this, lc1] >= 0.5) &&
  packedRight[this, rc1] &&
(fracRight[this, rc1] >= 0.5) && 
 (count[this] == lc1+rc1+1) )
)
 ==> countPredFunc(this, count,  lc1, rc1, 
        packedLeft, fracLeft, packedRight, fracRight)
) 
);

procedure ConstructComposite(this:Ref);
	ensures (count[this] == 1) &&
		(left[this] == null) &&
		(right[this] == null) &&
		(parent[this] == null);
 
 procedure updateCount(this: Ref)
 modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;

 requires this != null;
 requires ( packedLeft[this, count[left[this]]] &&
 	  packedRight[this, count[right[this]]] &&
 	  (fracLeft[this, count[left[this]]] >= 0.5) && 
	 (fracRight[this, count[right[this]]] >= 0.5) && 
	(fracCount[this, count[this]] == 1.0) );
// Might put count[this] instead of c here.        
// ensures ( exists c:int :: packedCount[this, c] && (fracCount[this, c] == 1.0));  
ensures (packedCount[this, count[this]] && 
	(fracCount[this, count[this]] == 1.0)); 
{
   var newc:int;
   newc := 1;


        if (left[this] != null)
           {
 	call UnpackLeftNotNull(this, count[left[this]]);
	packedLeft[this, count[left[this]]] := false;
	call UnpackCount(left[this], count[left[this]]);
	packedCount[left[this], count[left[this]]] := false; 
        newc := newc + count[left[this]];
	call PackCount(left[this], count[left[this]]);
	packedCount[left[this], count[left[this]]]:=true;
       }
       
        if (right[this] != null)
             {
         call UnpackRightNotNull(this, count[right[this]]);
	 packedRight[this, count[right[this]]] := false;
	call UnpackCount(right[this], count[right[this]]);
         newc := newc + count[right[this]];
         
       }
        
    count[this] := newc;   
       
 
    packedCount[this, count[this]]:=true;
    
}


procedure updateCountRec(this: Ref)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires (this != null);
requires packedParent[this] == false;
requires (parent[this] != null) ==> (fracParent[parent[this]] > 0.0);
requires (parent[this] != null) && (this==right[parent[this]]) ==> 
	(fracRight[parent[this], count[right[parent[this]]]] >= 0.5);
requires (parent[this] != null) && (this==left[parent[this]]) ==> 
	(fracLeft[parent[this], count[left[parent[this]]]] >= 0.5);
requires (parent[this] == null) ==> (fracCount[this, count[this]] >= 0.5);
requires (forall r:Ref :: (r!=this) ==> packedCount[r, count[this]]);
requires packedLeft[this, count[left[this]]];
requires packedRight[this, count[right[this]]];
requires (fracLeft[this, count[left[this]]] >= 0.5) && 
	(fracRight[this, count[right[this]]] >= 0.5);
requires (fracCount[this, count[this]] >= 0.5);

ensures   (packedParent[this]);    

{
 var fracLocalCount: [Ref, int]real;
 var fracLocalRight: [Ref, int]real;
 var fracLocalLeft: [Ref, int]real;

  if (parent[this] != null)
 {

fracLocalCount[this, count[this]]:=fracCount[this, count[this]];

//we unpack parent[this] from parentP
//might need to say that other objects are not unpacked for parentP
packedParent[parent[this]] := false;

//we can assume this because we just unpacked
//parent[this] from parentP
assume fracCount[parent[this], count[parent[this]]] >= 0.5;
fracLocalCount[parent[this], count[parent[this]]] := fracCount[parent[this], count[parent[this]]];


//we unpack parent[this] from countP
packedCount[parent[this], count[parent[this]]]:=false;

//we can assume this because we just unpacked parent[this] from countP
assume (fracLeft[this, count[left[this]]] >= 0.5) && (fracRight[this, count[right[this]]] >= 0.5);
fracLocalRight[parent[this], count[right[parent[this]]]] := fracRight[parent[this],  count[right[parent[this]]]];


//we assume this is the right child of parent[this]
//the other case is analogous
assume this==right[parent[this]];

fracLocalRight[parent[this], count[right[parent[this]]]] := 
	fracLocalRight[parent[this], count[right[parent[this]]]] +
	fracRight[parent[this], count[right[parent[this]]]];

//unpack parent[this] from rightP
packedRight[parent[this], count[right[parent[this]]]] := false;

fracLocalCount[this, count[this]] := fracLocalCount[this, count[this]] + fracCount[this, count[this]];

fracCount[this, count[this]] := fracLocalCount[this, count[this]];

packedRight[this, count[right[this]]] := true;

packedLeft[this, count[left[this]]] := true;
      call updateCount(this);


packedParent[parent[this]] := false;

assume parent[parent[this]] != null ==> ( fracParent[parent[parent[this]]] > 0.0);
assume parent[parent[this]] == null ==> (fracCount[parent[this], count[parent[this]]] >= 0.5);
assume (parent[parent[this]] != null) && (this==right[parent[parent[this]]]) ==> 
	(fracRight[parent[parent[this]], count[right[parent[parent[this]]]]] >= 0.5);
assume (parent[parent[this]] != null) && (this==left[parent[parent[this]]]) ==> 
	(fracLeft[parent[parent[this]], count[left[parent[parent[this]]]]] >= 0.5);


packedRight[parent[this], count[right[parent[this]]]] := true;

assume left[parent[this]] != null;

assume packedCount[left[parent[this]], count[left[parent[this]]]] && 
	(count[left[parent[this]]] == count[this]);
 
packedLeft[parent[this],count[left[parent[this]]]] := true;
      call updateCountRec(parent[this]);
      }
    else
  { 
fracLocalCount[this, count[this]] := fracCount[this, count[this]];
fracLocalCount[this, count[this]] := fracLocalCount[this, count[this]] + fracCount[this, count[this]];
fracCount[this, count[this]] := fracLocalCount[this, count[this]];    
 
         call updateCount(this);

  }  
 }



procedure setLeft(this: Ref, l:Ref)
modifies parent, left, count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires this!=null;
requires this!=l;
requires l!=null;
requires packedParent[this];
requires packedParent[l];
requires (forall r:Ref:: packedCount[r, count[r]]);
ensures packedParent[this];
 {

packedParent[this]:=false;


   parent[l]:=this;
   left[this]:=l;


packedLeft[this, count[left[this]]] := true;

packedRight[this, count[right[this]]] := true;

packedCount[this, count[this]] := false;

call updateCountRec(this);
   
}

