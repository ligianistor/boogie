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

procedure PackLeftNotNull(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this] == false);
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (left[this] != null);
requires (left[this] == ol);
requires (fracCount[ol] == 0.5);  

procedure PackLeftNull(this:Ref, ol:Ref, lc:int);
requires (packedLeft[this] == false);
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (left[this] == null);
requires (left[this] == ol);
requires (lc == 0);

procedure UnpackLeftNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (fracLeft[this] > 0.0);
requires (left[this] == null);
ensures (left[this] == ol);
ensures (paramCountC[ol] == lc);
ensures	(lc == 0);

procedure UnpackLeftNotNull(this:Ref, ol:Ref, lc:int);
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires (fracLeft[this] > 0.0);
requires (left[this] != null);
ensures  (fracCount[ol] == 0.5);
ensures (paramCountC[ol] == lc);
ensures	(left[this] == ol);

procedure PackRightNotNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this] == false);
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (right[this] != null);
requires (right[this] == or);
requires (fracCount[or] == 0.5) ;

procedure PackRightNull(this:Ref, or:Ref, rc:int);
requires (packedRight[this] == false);
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (rc == 0);
requires (right[this] == or);
requires (right[this] == null);

procedure UnpackRightNull(this:Ref, or:Ref, rc:int);
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (fracRight[this] > 0.0);
requires (right[this] == null);
ensures (rc == 0);
ensures (right[this] == or);
ensures (paramCountC[or] == rc);

procedure UnpackRightNotNull(this:Ref, or:Ref, rc:int);
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (fracRight[this] > 0.0);
requires (right[this] != null);
ensures (fracCount[or] == 0.5);
ensures  (right[this] == or);
ensures (paramCountC[or] == rc);

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
       
ensures ( exists c3:int :: packedCount[this] && (fracCount[this] == 1.0) && (paramCountC[this] == c3));  
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
	packedLeft[this] := false;
//This should be in a forall in the requires of the procedure.
	packedCount[ol] := true;
	
	call UnpackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol] := false; 
        newc := newc + count[left[this]];
	assert (newc == 1 + c1);
	call PackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol]:=true;
       }
	assert (newc == 1 + c1);       

        if (right[this] != null)
             {
         call UnpackRightNotNull(this, or, c2);
	 packedRight[this] := false;
//Here it is easy to come up with ol2, or2, lc2, rc2 because they can be arbitrary.
//Again, this should be in the requires of thsi procedure.
	packedCount[or] := true;
	call UnpackCount(or, c2, ol2, or2, lc2, rc2);
         newc := newc + count[right[this]]; 
	assert (newc == 1 + c1 + c2);
       }
assert (newc == 1 + c1 + c2);
    count[this] := newc; 
    //We update the corresponding paramCount for that field
    //whenever we update a field.
    paramCountC[this] := newc;  
//Here it is difficult because this is the phase where we need to use what we know and 
//instantiate the exists with the right values.
    call PackCount(this, newc, ol, or, c1, c2);
    packedCount[this]:=true;
//Maybe we need an axiom that ties newc with the c3 that the ensures exists expects.
    
}
