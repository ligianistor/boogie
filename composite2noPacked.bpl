type Ref;

const null: Ref;

var left : [Ref]Ref;
var right : [Ref]Ref;
var parent : [Ref]Ref;
var count : [Ref]int;

var packedCount : [Ref, int] bool;
var packedLeft : [Ref, Ref, int] bool;
var packedRight : [Ref, Ref, int] bool;
var packedParent : [Ref] bool;

var fracCount : [Ref, int] real;
var fracLeft : [Ref, Ref, int] real;
var fracRight : [Ref, Ref, int] real;
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

procedure PackLeftNotNull(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this, ol, lc] == false) &&
	 (left[this] != null) && 
	(left[this] == ol) &&
       (fracCount[ol, lc] == 0.5);  

procedure PackLeftNull(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this, ol, lc] == false) &&
	 (left[this] == null) && 
	 (left[this] == ol) &&
	 (lc == 0);

procedure UnpackLeftNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this, ol, lc] && 
	(fracLeft[this, ol, lc] > 0.0) &&
	(left[this] == null);
ensures (left[this] == ol) &&
	(lc == 0);

procedure UnpackLeftNotNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this, ol, lc] && 
	 (fracLeft[this, ol, lc] > 0.0) && 
	 (left[this] != null);
ensures  (fracCount[ol, lc] == 0.5) &&
	(left[this] == ol);

procedure PackRightNotNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this, or, rc] == false) &&
	 (right[this] != null) && 
	(right[this] == or) &&
         (fracCount[or, rc] == 0.5) ;

procedure PackRightNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this, or, rc] == false) &&
	 (rc == 0) &&
	 (right[this] == or) &&
	 (right[this] == null);

procedure UnpackRightNull(this:Ref, or:Ref, rc:int);
requires packedRight[this, or, rc] && 
	(fracRight[this, or, rc] > 0.0) && 
	(right[this] == null);
ensures (rc == 0) && (right[this] == or);

procedure UnpackRightNotNull(this:Ref, or:Ref, rc:int);
requires packedRight[this, or, rc] && 
	(fracRight[this, or, rc] > 0.0) && 
	(right[this] != null);
ensures (fracCount[or, rc] == 0.5) && (right[this] == or);

procedure PackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires (packedCount[this, c] == false) &&
	 (this!=null) && 
	(count[this] == c) &&
	(fracLeft[this, ol, lc] == 0.5) &&
	(fracRight[this, or, rc] == 0.5) && 
 	(c == lc + rc + 1);

procedure UnpackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires packedCount[this, c] && 
	(fracCount[this, c] > 0.0);
ensures (this!=null) && 
	(count[this] == c) &&
 (fracLeft[this, ol, lc] == 0.5) &&
 (fracRight[this, or, rc] == 0.5) && 
 (c == lc + rc + 1);


//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref, c:int);
requires (packedParent[this] == false) &&
	(parent[this] != this) &&
     (fracCount[this, c] == 0.5) &&
     (parent[this] != null) &&
     (fracParent[parent[this]] > 0.0) &&
            (
           ((fracLeft[parent[this], this, c] == 0.5))
             ||
           ((fracRight[parent[this], this, c] == 0.5))
           );

procedure PackParentNull(this:Ref, c:int);
requires (packedParent[this] == false) &&
	(parent[this] != this) &&
   (fracCount[this, c] == 1.0) &&
    packedCount[this, c] &&
   (parent[this]==null);

procedure UnpackParent(this:Ref, c:int);
requires packedParent[this] &&
	(fracParent[this] > 0.0);
ensures (parent[this] != this)
       &&        
     (( packedCount[this,c] &&
     (fracCount[this, c] == 0.5)
     &&
     ((parent[this] != null) ==>
            ((fracParent[parent[this]] > 0.0) &&
            (((fracLeft[parent[this], this, c] == 0.5))
             ||
           ((fracRight[parent[this], this, c] == 0.5))
           ) ) )
     &&
     ((parent[this]==null) ==> (fracCount[this,c] == 0.5) )  ) );


procedure ConstructComposite(this:Ref);
	ensures (count[this] == 1) &&
		(left[this] == null) &&
		(right[this] == null) &&
		(parent[this] == null);
 
procedure updateCount(this: Ref, c:int, c1:int, c2:int, ol:Ref, or:Ref)
 modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;

 requires this != null;
 requires (packedLeft[this, ol, c1] &&
 	 packedRight[this, or, c2] &&
 	 (fracLeft[this, ol, c1] == 0.5) && 
	 (fracRight[this, or, c2] == 0.5) && 
	 (fracCount[this, c] == 1.0) ) ;
       
ensures ( exists c:int :: packedCount[this, c3] && (fracCount[this, c3] == 1.0));  
{
   var newc:int;
   newc := 1;


        if (left[this] != null)
           {
 	call UnpackLeftNotNull(this, left[this], count[left[this]]);
	packedLeft[this, left[this], count[left[this]]] := false;
	call UnpackCount(left[this], count[left[this]]);
	packedCount[left[this], count[left[this]]] := false; 
        newc := newc + count[left[this]];
	call PackCount(left[this], count[left[this]]);
	packedCount[left[this], count[left[this]]]:=true;
       }
       
        if (right[this] != null)
             {
         call UnpackRightNotNull(this, right[this], count[right[this]]);
	 packedRight[this, right[this], count[right[this]]] := false;
	call UnpackCount(right[this], count[right[this]]);
         newc := newc + count[right[this]]; 
       }

    count[this] := newc;   
    packedCount[this, count[this]]:=true;
    
}


procedure updateCountRec(this: Ref, opp: Ref, lcc:int, ol:Ref, or:Ref, lc:int, rc:int)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires (this != null);
requires packedParent[this] == false;
requires (opp == parent[this]);
requires (opp != null) ==> (fracParent[opp] > 0.0);
requires (opp != null) && (this==right[opp]) ==> 
	(fracRight[opp, this, lcc] == 0.5);
requires (opp != null) && (this==left[opp]) ==> 
	(fracLeft[opp, this, lcc] == 0.5);
requires (opp == null) ==> (fracCount[this, lcc] == 0.5);
requires (forall r:Ref :: (r!=this) ==> packedCount[r, count[this]]);
requires packedLeft[this, ol, lc];
requires packedRight[this, or, rc];
requires (fracLeft[this, ol, lc] == 0.5) && 
	(fracRight[this, or, rc] == 0.5);
requires (fracCount[this, lcc] == 0.5);

ensures   (packedParent[this]);    

{
 var fracLocalCount: [Ref, int]real;
 var fracLocalRight: [Ref, Ref, int]real;
 var fracLocalLeft: [Ref, Ref, int]real;

  if (parent[this] != null)
 {

fracLocalCount[this, count[this]]:=fracCount[this, count[this]];

//we unpack parent[this] from parentP
//might need to say that other objects are not unpacked for parentP
packedParent[parent[this]] := false;

//we can assume this because we just unpacked
//parent[this] from parentP
assume fracCount[parent[this], count[parent[this]]] == 0.5;
fracLocalCount[parent[this], count[parent[this]]] := fracCount[parent[this], count[parent[this]]];


//we unpack parent[this] from countP
packedCount[parent[this], count[parent[this]]]:=false;

//we can assume this because we just unpacked parent[this] from countP
assume (fracLeft[this, left[this], count[left[this]]] == 0.5) && (fracRight[this, right[this], count[right[this]]] == 0.5);
fracLocalRight[parent[this], right[parent[this]], count[right[parent[this]]]] := fracRight[parent[this], right[parent[this]],  count[right[parent[this]]]];


//we assume this is the right child of parent[this]
//the other case is analogous
assume this==right[parent[this]];

fracLocalRight[parent[this], right[parent[this]], count[right[parent[this]]]] := 
	fracLocalRight[parent[this], right[parent[this]], count[right[parent[this]]]] +
	fracRight[parent[this], right[parent[this]], count[right[parent[this]]]];

//unpack parent[this] from rightP
packedRight[parent[this], right[parent[this]], count[right[parent[this]]]] := false;

fracLocalCount[this, count[this]] := fracLocalCount[this, count[this]] + fracCount[this, count[this]];

fracCount[this, count[this]] := fracLocalCount[this, count[this]];

packedRight[this, right[this], count[right[this]]] := true;

packedLeft[this, left[this], count[left[this]]] := true;
      call updateCount(this);


packedParent[parent[this]] := false;

assume parent[parent[this]] != null ==> ( fracParent[parent[parent[this]]] > 0.0);
assume parent[parent[this]] == null ==> (fracCount[parent[this], count[parent[this]]] == 0.5);
assume (parent[parent[this]] != null) && (this==right[parent[parent[this]]]) ==> 
	(fracRight[parent[parent[this]], right[parent[parent[this]]], count[right[parent[parent[this]]]]] == 0.5);
assume (parent[parent[this]] != null) && (this==left[parent[parent[this]]]) ==> 
	(fracLeft[parent[parent[this]], left[parent[parent[this]]], count[left[parent[parent[this]]]]] == 0.5);


packedRight[parent[this], right[parent[this]], count[right[parent[this]]]] := true;

assume left[parent[this]] != null;

assume packedCount[left[parent[this]], count[left[parent[this]]]] && 
	(count[left[parent[this]]] == count[this]);
 
packedLeft[parent[this], left[parent[this]], count[left[parent[this]]]] := true;
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
if (parent[l] == null) {
	packedParent[this]:=false;

   	parent[l]:=this;
   	left[this]:=l;

	packedLeft[this, left[this], count[left[this]]] := true;

	packedRight[this, right[this], count[right[this]]] := true;

	packedCount[this, count[this]] := false;

	call updateCountRec(this);
}
   
}

