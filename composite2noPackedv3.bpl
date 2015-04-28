type Ref;

const null: Ref;

var left : [Ref]Ref;
var right : [Ref]Ref;
var parent : [Ref]Ref;
var count : [Ref]int;

var packedCount : [Ref] bool;
var packedLeft : [Ref] bool;
var packedRight : [Ref] bool;
var packedParent : [Ref] bool;

var fracCount : [Ref] real;
var fracLeft : [Ref] real;
var fracRight : [Ref] real;
var fracParent : [Ref] real;

// The reasoning for having params[] instead of putting the parameters 
// in packed[..] and frac[..] is that if we have 
// packedCount[this,c] == false the precondition of updateCount() and 
// then inside the procedure I need packedCount[this,newc] == false, this
// object proposition is still unpacked but just the parameter changed.
// packedCount[] should mean the access to the field count, we don't care about what are the actual values
// of the fields.
// I still need it to be unpacked, but with a different parameter.
// They are different things so they should be separate.

var paramCountC : [Ref]int;
var paramLeftOl : [Ref]Ref;
var paramLeftLc : [Ref]int;
var paramRightOr : [Ref]Ref;
var paramRightRc : [Ref]int;

//axiom that shows there are no cycles in the tree, locally
//this axiom describes the data structure, does not depend on whether 
//a predicate holds or not
axiom (forall this: Ref, l:Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=right[this]) && (this!=left[this]) && (this!=parent[this]));

//axiom stating that this is a binary tree
axiom (forall this: Ref, left: [Ref]Ref, right: [Ref]Ref, parent:[Ref]Ref::
    (this!=null) && (parent[this]!=null) ==>((this==right[parent[this]]) || (this==left[parent[this]]))
);

procedure PackLeft(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this] == false);
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (left[this] == ol);
requires (left[this] != null) ==> (fracCount[ol] == 0.5);
requires (left[this] == null) ==> (lc == 0);

procedure UnpackLeft(this:Ref, ol:Ref, lc:int);
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (fracLeft[this] > 0.0);
ensures	(left[this] == ol);
ensures (paramCountC[ol] == lc);
ensures (left[this] == null) ==> (lc == 0);
ensures (left[this] != null) ==> (fracCount[ol] == 0.5);

procedure PackRight(this:Ref, or:Ref, rc:int);
requires (packedRight[this] == false);
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (right[this] == or);
requires (right[this] != null) ==> (fracCount[or] == 0.5);
requires (right[this] == null) ==> (rc == 0);

procedure UnpackRight(this:Ref, or:Ref, rc:int);
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (fracRight[this] > 0.0);
ensures (right[this] == or);
ensures (paramCountC[or] == rc);
ensures (right[this] == null) ==> (rc == 0);
ensures (right[this] != null) ==> (fracCount[or] == 0.5);

procedure PackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires (packedCount[this] == false);
requires (paramCountC[this] == c);
requires (this!=null);
requires (count[this] == c);
requires (fracLeft[this] == 0.5);
requires (fracRight[this] == 0.5);
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (c == lc + rc + 1);

procedure UnpackCount(this:Ref, c:int, ol: Ref, or:Ref, lc:int, rc:int);
requires packedCount[this];
requires (paramCountC[this] == c);
requires (fracCount[this] > 0.0);
ensures (this!=null);
ensures	(count[this] == c);
ensures (fracLeft[this] == 0.5);
ensures (fracRight[this] == 0.5);
ensures (paramRightOr[this] == or);
ensures (paramRightRc[this] == rc);
ensures (paramLeftOl[this] == ol);
ensures (paramLeftLc[this] == lc);
ensures (c == lc + rc + 1);


//maybe we do not need this axiom now
axiom (forall this:Ref,count: [Ref]int :: (this==null) ==> (count[this]==0)  );

procedure PackParentNotNull(this:Ref, c:int);
requires (packedParent[this] == false);
requires (parent[this] != this);
requires (fracCount[this] == 0.5);
requires (paramCountC[this] == c);
requires (parent[this] != null);
requires (fracParent[parent[this]] > 0.0);
requires  (  	(fracLeft[parent[this]] == 0.5) && 
	     	(paramLeftOl[parent[this]] == this) && 
             	(paramLeftLc[parent[this]] == c)
	  )
          ||
          (
	     	(fracRight[parent[this]] == 0.5) && 
		(paramRightOr[parent[this]] == this) && 
		(paramRightRc[parent[this]] == c)
	  );

procedure PackParentNull(this:Ref, c:int);
requires (packedParent[this] == false);
requires (parent[this] != this);
requires (fracCount[this] == 1.0);
requires (paramCountC[this] == c);
requires packedCount[this];
requires (parent[this]==null);

procedure UnpackParent(this:Ref, c:int);
requires packedParent[this];
requires (fracParent[this] > 0.0);
ensures (parent[this] != this);
ensures packedCount[this];
ensures (paramCountC[this] == c);
ensures (fracCount[this] == 0.5);
ensures (parent[this] != null) ==>
            (
	   (fracParent[parent[this]] > 0.0) &&
            (
	(	(fracLeft[parent[this]] == 0.5) && 
		(paramLeftOl[parent[this]] == this) && 
		(paramLeftLc[parent[this]] == c)
	)
             ||
	(	(fracRight[parent[this]] == 0.5) && 
		(paramRightOr[parent[this]] == this) && 
		(paramRightRc[parent[this]] == c)
	)
           ) 
	   );
ensures (parent[this]==null) ==> ((fracCount[this] == 0.5) && (paramCountC[this] == c));

//---start of methods

procedure ConstructComposite(this:Ref);
ensures (count[this] == 1);
ensures	(left[this] == null);
ensures	(right[this] == null);
ensures	(parent[this] == null);


function funcParamCountC(c3:int, this:Ref, paramCountC:[Ref]int) returns (bool);

axiom ( forall c3:int, this:Ref,  paramCountC:[Ref]int ::
(
(paramCountC[this] == c3) ==> funcParamCountC(c3, this, paramCountC)
)
);
 
procedure updateCount(this: Ref, c:int, c1:int, c2:int, ol:Ref, or:Ref)
modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight, paramCountC;

requires this != null;
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == c1);
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == c2);
requires (fracLeft[this] == 0.5);
requires (fracRight[this] == 0.5); 
requires (fracCount[this] == 1.0);
requires (paramCountC[this] == c);
requires (packedCount[this] == false);
ensures (fracCount[this] == 1.0);
ensures packedCount[this];
ensures (exists c3:int :: funcParamCountC(c3, this, paramCountC));  
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
//In the source java code, the programmer can use 
// unpack(ol#1/2 count(c1)), where ol appears in the exists
//
//We need to do the unpacking of left before the if
//because we use left[this] in the condition of the if,
//that is we access the field left of this.
//For this we need the field to be accessible, unpacked.
 	call UnpackLeft(this, ol, c1);
	packedLeft[this] := false;

        if (left[this] != null)
           {
//This should be in a forall in the requires of the procedure.
	packedCount[ol] := true;
	
	call UnpackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol] := false; 
        newc := newc + count[left[this]];
	call PackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol]:=true;
	assert newc == 1 + c1;
       }
   
        call UnpackRight(this, or, c2);
	packedRight[this] := false;
    
        if (right[this] != null)
             {

//Here it is easy to come up with ol2, or2, lc2, rc2 because they can be arbitrary.
//Again, this should be in the requires of thsi procedure.
	packedCount[or] := true;
	call UnpackCount(or, c2, ol2, or2, lc2, rc2);
         newc := newc + count[right[this]]; 
       }

    count[this] := newc; 
    //We update the corresponding paramCount for that field
    //whenever we update a field.
    paramCountC[this] := newc;  
//Here it is difficult because this is the phase where we need to use what we know and 
//instantiate the exists with the right values.
    call PackCount(this, newc, ol, or, c1, c2);
    packedCount[this]:=true;

//We need this assert otherwise Boogie does not know the value with which 
//it should instantiate c3 from the post-condition.
//TODO I need to find a way to generate this assert and the most likely value 
//for c3.
assert funcParamCountC(newc, this, paramCountC);
    
}
//TODO next procedure to prove

procedure updateCountRec(this: Ref, opp: Ref, lcc:int, ol:Ref, or:Ref, lc:int, rc:int)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires (this != null);
requires packedParent[this] == false;
requires (opp == parent[this]);
requires (fracParent[this] > 0.0);
requires (opp != null) ==> (fracParent[opp] > 0.0) && 
			   packedParent[opp];
requires (opp != null) && (this==right[opp]) ==> 
	((fracRight[opp] == 0.5) && 
	(paramRightOr[opp] == this) && 
	(paramRightRc[this] == lcc));
requires (opp != null) && (this==left[opp]) ==> 
	((fracLeft[opp] == 0.5) && 
	(paramLeftOl[opp] == this) && 
	(paramLeftLc[this] == lcc));
requires (opp == null) ==> ((fracCount[this] == 0.5) && 
			    (paramCountC[this] == lcc));
requires (forall r:Ref :: (r!=this) ==> (packedCount[r] && (paramCountC[r] == count[this])));
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (fracLeft[this] == 0.5);
requires (fracRight[this] == 0.5);
requires (fracCount[this] == 0.5);
requires (paramCountC[this] == lcc);

ensures   (packedParent[this]);    

{
 var fracLocalCount: [Ref]real;
 var fracLocalRight: [Ref]real;
 var fracLocalLeft: [Ref]real;

  if (parent[this] != null)
 {

fracLocalCount[this] := fracCount[this];

//we unpack parent[this] from parentP
//might need to say that other objects are not unpacked for parentP
packedParent[opp] := false;


//we unpack parent[this] from countP
packedCount[opp]:=false;

      call updateCountRec(parent[this]);
      }
    else
  { 
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
requires (forall r:Ref:: packedCount[r] && (paramCountC[r] == count[r]));
ensures packedParent[this];
 {
if (parent[l] == null) {
	packedParent[l]:=false;

   	parent[l]:=this;
   	left[this]:=l;

	call updateCountRec(this);
}
   
}

