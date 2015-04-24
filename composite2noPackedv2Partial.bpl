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
requires (packedLeft[this, ol, lc] == false);
requires (left[this] != null);
requires (left[this] == ol);
requires (fracCount[ol, lc] == 0.5);  

procedure PackLeftNull(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this, ol, lc] == false);
requires (left[this] == null);
requires (left[this] == ol);
requires (lc == 0);

procedure UnpackLeftNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this, ol, lc];
requires (fracLeft[this, ol, lc] > 0.0);
requires (left[this] == null);
ensures (left[this] == ol);
ensures	(lc == 0);

procedure UnpackLeftNotNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this, ol, lc];
requires (fracLeft[this, ol, lc] > 0.0);
requires (left[this] != null);
ensures  (fracCount[ol, lc] == 0.5);
ensures	(left[this] == ol);

procedure PackRightNotNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this, or, rc] == false);
requires (right[this] != null);
requires (right[this] == or);
requires (fracCount[or, rc] == 0.5) ;

procedure PackRightNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this, or, rc] == false);
requires (rc == 0);
requires (right[this] == or);
requires (right[this] == null);

procedure UnpackRightNull(this:Ref, or:Ref, rc:int);
requires packedRight[this, or, rc];
requires (fracRight[this, or, rc] > 0.0);
requires (right[this] == null);
ensures (rc == 0);
ensures (right[this] == or);

procedure UnpackRightNotNull(this:Ref, or:Ref, rc:int);
requires packedRight[this, or, rc];
requires (fracRight[this, or, rc] > 0.0);
requires (right[this] != null);
ensures (fracCount[or, rc] == 0.5);
ensures  (right[this] == or);

procedure PackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires (packedCount[this, c] == false);
requires (this!=null);
requires (count[this] == c);
requires (fracLeft[this, ol, lc] == 0.5);
requires (fracRight[this, or, rc] == 0.5);
requires (c == lc + rc + 1);

procedure UnpackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires packedCount[this, c];
requires (fracCount[this, c] > 0.0);
ensures (this!=null);
ensures	(count[this] == c);
ensures (fracLeft[this, ol, lc] == 0.5);
ensures (fracRight[this, or, rc] == 0.5);
ensures (c == lc + rc + 1);


//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref, c:int);
requires (packedParent[this] == false);
requires (parent[this] != this);
requires (fracCount[this, c] == 0.5);
requires (parent[this] != null);
requires (fracParent[parent[this]] > 0.0);
requires  (fracLeft[parent[this], this, c] == 0.5)
             ||
           (fracRight[parent[this], this, c] == 0.5);

procedure PackParentNull(this:Ref, c:int);
requires (packedParent[this] == false);
requires (parent[this] != this);
requires (fracCount[this, c] == 1.0);
requires packedCount[this, c];
requires (parent[this]==null);

procedure UnpackParent(this:Ref, c:int);
requires packedParent[this];
requires (fracParent[this] > 0.0);
ensures (parent[this] != this);
ensures packedCount[this,c];
ensures (fracCount[this, c] == 0.5);
ensures (parent[this] != null) ==>
            (
	   (fracParent[parent[this]] > 0.0) &&
            (
	   (fracLeft[parent[this], this, c] == 0.5)
             ||
           (fracRight[parent[this], this, c] == 0.5)
           ) 
	   );
ensures (parent[this]==null) ==> (fracCount[this,c] == 0.5);

//---start of methods

procedure ConstructComposite(this:Ref);
ensures (count[this] == 1);
ensures	(left[this] == null);
ensures	(right[this] == null);
ensures	(parent[this] == null);
 
procedure updateCount(this: Ref, c:int, c1:int, c2:int, ol:Ref, or:Ref)
modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;

requires this != null;
requires packedLeft[this, ol, c1];
requires packedRight[this, or, c2];
requires (fracLeft[this, ol, c1] == 0.5);
requires (fracRight[this, or, c2] == 0.5); 
requires (fracCount[this, c] == 1.0);
requires (packedCount[this, c] == false);
       
ensures ( exists c3:int :: packedCount[this, c3] && (fracCount[this, c3] == 1.0));  
{
   var newc : int;
//All variable declarations must be made before the code starts.
  var ol1: Ref;
  var or1:Ref;
  var lc1:int;
  var rc1:int;

  var ol2: Ref;
  var or2:Ref;
  var lc2:int;
  var rc2:int;

   newc := 1;

        if (left[this] != null)
           {
//In the source java code, the programmer can use 
// unpack(ol#1/2 count(c1)), where ol appears in the exists
 	call UnpackLeftNotNull(this, ol, c1);
	packedLeft[this, ol, c1] := false;
//This should be in a forall in the requires of the procedure.
	packedCount[ol, c1] := true;
	call UnpackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol, c1] := false; 
        newc := newc + count[left[this]];
	call PackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol, c1]:=true;
       }
       
        if (right[this] != null)
             {
         call UnpackRightNotNull(this, or, c2);
	 packedRight[this, or, c2] := false;
//Here it is easy to come up with ol2, or2, lc2, rc2 because they can be arbitrary.
//Again, this should be in the requires of thsi procedure.
	packedCount[or, c2] := true;
	call UnpackCount(or, c2, ol2, or2, lc2, rc2);
         newc := newc + count[right[this]]; 
       }

    count[this] := newc;   
//Here it is difficult because this is the phase where we need to use what we know and 
//instantiate the exists with the right values.
    call PackCount(this, newc, ol, or, c1, c2);
    packedCount[this, newc]:=true;
//Maybe we need an axiom that ties newc with the c3 that the ensures exists expects.
    
}
