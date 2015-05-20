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

procedure PackParent(this:Ref, c:int);
requires (packedParent[this] == false);
requires (parent[this] != this);
requires (fracCount[this] == 0.5);
requires (paramCountC[this] == c);
requires (fracParent[parent[this]] > 0.0);
requires  (parent[this] != null) ==>
	((fracLeft[parent[this]] == 0.5) && 
	     	(paramLeftOl[parent[this]] == this) && 
             	(paramLeftLc[parent[this]] == c)
	  )
          ||
          (
	     	(fracRight[parent[this]] == 0.5) && 
		(paramRightOr[parent[this]] == this) && 
		(paramRightRc[parent[this]] == c)
	  );
requires (parent[this]==null) ==> ((fracCount[this] == 0.5) && packedCount[this]);


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

procedure updateCount(this: Ref, c:int, ol:Ref, or:Ref, c1:int, c2:int)
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
requires (forall y:Ref :: ( ( (y!=this) && (parent[this]!=y) ) ==> (packedCount[y] ) ) );
requires packedCount[ol];
requires packedCount[or];
ensures (fracCount[this] == 1.0);
ensures packedCount[this];
ensures (paramCountC[this] == c1 + c2 + 1 );  
ensures (forall y:Ref :: (fracRight[y] == old(fracRight[y]) ) );
ensures (forall y:Ref :: (paramRightOr[y] == old(paramRightOr[y]) ) );
ensures (forall y:Ref :: (paramRightRc[y] == old(paramRightRc[y]) ) );
ensures (forall y:Ref :: (paramLeftOl[y] == old(paramLeftOl[y]) ) );
ensures (forall y:Ref :: (paramLeftLc[y] == old(paramLeftLc[y]) ) );
ensures (forall y:Ref :: (fracLeft[y] == old(fracLeft[y]) ) );
ensures (forall y:Ref :: (packedRight[y] == old(packedRight[y]) ) );
ensures (forall y:Ref :: (packedLeft[y] == old(packedLeft[y]) ) );
ensures (forall y:Ref :: (fracCount[y] == old(fracCount[y]) ) );
ensures (forall y:Ref :: (packedParent[y] == old(packedParent[y]) ) );
ensures (forall y:Ref :: ((y!=this) ==> (paramCountC[y] == old(paramCountC[y]) ) ) );
ensures (forall y:Ref :: ((y!=this) ==> (packedCount[y] == old(packedCount[y]) ) ) );
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
	
	call UnpackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol] := false; 
        newc := newc + count[left[this]];
	call PackCount(ol, c1, ol1, or1, lc1, rc1);
	packedCount[ol]:=true;
       }
 	call PackLeft(this, ol, c1);
	packedLeft[this] := true;
   
        call UnpackRight(this, or, c2);
	     packedRight[this] := false;
    
        if (right[this] != null)
             {

//Here it is easy to come up with ol2, or2, lc2, rc2 because they can be arbitrary.
	call UnpackCount(or, c2, ol2, or2, lc2, rc2);
         newc := newc + count[right[this]]; 
       }

        call PackRight(this, or, c2);
	packedRight[this] := true;
    

    count[this] := newc; 
    //We update the corresponding paramCount for that field
    //whenever we update a field.
    paramCountC[this] := newc;  
//Here it is difficult because this is the phase where we need to use what we know and 
//instantiate the exists with the right values.
//Here we need to use the fraction to right(this).
    call PackCount(this, newc, ol, or, c1, c2);
    packedCount[this]:=true;
    
}

procedure updateCountRec(this: Ref, opp: Ref, lcc: int, ol: Ref, or: Ref, lc: int, rc: int)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight, paramCountC, paramLeftOl, paramLeftLc, paramRightRc;
requires (this != null);
requires ol!=opp;
requires or!=opp;
requires packedParent[this] == false;
// We only have  these 2 object propositions unpacked at the same time
requires (forall y:Ref :: ( ((y!=this) && (y!=opp) ) ==> packedParent[y]));
requires (forall y:Ref ::  ((y!=this) ==> packedCount[y]));
requires (forall y:Ref ::  ((y!=this) ==> packedLeft[y]) );
requires (packedCount[this] == false);
// These foralls should be put in by the programmer,
// because it is implicit only that everything that is not unpacked is packed.
// IT's just a small step that the programmer could put in.
requires (forall y:Ref :: ( fracParent[y] > 0.0 ));
requires (parent[this] == opp);
requires (fracParent[this] > 0.0);
requires (opp != null) ==> (fracParent[opp] > 0.0); 
requires (opp != null) ==> packedParent[opp];
requires (opp != null) ==> 
	( ((fracRight[opp] == 0.5) && 
	(paramRightOr[opp] == this) && 
	(paramRightRc[opp] == lcc))
  ||
  	((fracLeft[opp] == 0.5) && 
	(paramLeftOl[opp] == this) && 
	(paramLeftLc[opp] == lcc))
  );
  //Could add ==> packedCount[this] below but that
  //leads to inconsistencies similar to "requires false"
requires (opp == null) ==> ((fracCount[this] == 0.5) && 
			    (paramCountC[this] == lcc) );
requires packedLeft[this];
requires (paramLeftOl[this] == ol);
requires (paramLeftLc[this] == lc);
requires packedCount[ol];
requires packedCount[or];
requires packedRight[this];
requires (paramRightOr[this] == or);
requires (paramRightRc[this] == rc);
requires (fracLeft[this] == 0.5);
requires (fracRight[this] == 0.5);
requires (fracCount[this] == 0.5);
requires (paramCountC[this] == lcc);
requires (count[this] == lcc);
ensures (packedParent[this]);  
ensures (fracParent[this] > 0.0);  
{
var fracLocalCount : [Ref]real;
var fracLocalRight : [Ref]real;
var fracLocalLeft : [Ref]real;
var fracLocalParent : [Ref]real; 

// Existential variable for UnpackParent(opp, lccc)
var lccc : int;

// Existential variables for UnpackCount(opp, lccc)
var oll : Ref;
var orr : Ref;
var llc : int;
var rrc : int;

// Existential variables used in the parameters of call updateCountRec()
var oppp : Ref;
var olpar : Ref;
var lcpar : int; 

if (parent[this] != null) {
	// Split the fraction k of opp in parent.
	// fracLocalParent represents what is left over after the splitting
	// and after half is used.
	fracLocalParent[opp] := fracParent[opp] / 2.0;
	fracParent[opp] := fracParent[opp] / 2.0;

	call UnpackParent(opp, lccc);
	packedParent[opp] := false;
 

	// Instantiate orr==this and rrc==lcc;
	call UnpackCount(opp, lccc, oll, this, llc, lcc);
	packedCount[opp] := false;

	assume (this == right[opp]);

	//fracRight[opp] := 2.0 * fracRight[opp];
	
	// This should be in a forall in the pre-condition.
	packedRight[opp] := true;
	call UnpackRight(opp, this, lcc);
  assert (paramRightRc[opp] == paramCountC[this]);
	packedRight[opp] := false;

	fracCount[this] := fracCount[this] * 2.0;
	call updateCount(this, lcc, ol, or, lc, rc);
  // We need to ensure this connection between paramRightRc and paramCountC
  paramRightRc[parent[this]] := paramCountC[this];

  // We know that if right[opp] == this,
  // when paramCountC[this] changes, then paramRightRc[opp] also changes
 // paramRightRc[opp] := paramCountC[this];

  fracLocalCount[this] := fracCount[this] / 2.0;
  fracCount[this] := fracCount[this] / 2.0;
  assert parent[this] != null;
  
  assert (fracRight[parent[this]] == 0.5);
	assert (paramRightOr[parent[this]] == this);
  assert (paramCountC[this] == lc + rc + 1);
	assert (paramRightRc[parent[this]] == lc + rc + 1);
  

	call PackParent(this, lc + rc + 1);
	packedParent[this] := true;
	
	call PackRight(opp, this, lc + rc + 1);
	packedRight[opp] := true;

  // This assume says that there are no cycles in the tree.
  // Maybe can state it as an axiom.
  // Maybe the user needs to give a hint that
  // there are no cycles.

  
//This is added as part of the existential instantiation.
  paramLeftOl[opp] := olpar;
  paramLeftLc[opp] := lcpar;
  
assume olpar!=parent[opp];
assume olpar!=this;
assume olpar!=opp;

assert olpar!=parent[opp];
assert this!=parent[opp];
assert packedParent[opp] == false;
assert (forall y:Ref :: ( ((y!=opp) && (y!=parent[opp]) ) ==> packedParent[y]));
assert (forall y:Ref ::  ((y!=opp) ==> packedCount[y]));
assert (packedCount[opp] == false);
assert (forall y:Ref :: ( fracParent[y] > 0.0 ));
assert (parent[opp] == parent[opp]);
assert (fracParent[opp] > 0.0);
assert (parent[opp] != null) ==> (fracParent[parent[opp]] > 0.0); 
assert (parent[opp] != null) ==> packedParent[parent[opp]];
assert (parent[opp] != null) ==> 
	( ((fracRight[parent[opp]] == 0.5) && 
	(paramRightOr[parent[opp]] == opp) && 
	(paramRightRc[parent[opp]] == lccc))
  ||
  	((fracLeft[parent[opp]] == 0.5) && 
	(paramLeftOl[parent[opp]] == opp) && 
	(paramLeftLc[parent[opp]] == lccc))
  );
assert (parent[opp] == null) ==> ((fracCount[opp] == 0.5) && 
			    (paramCountC[opp] == lccc) );
assert opp != this;
assert (forall y:Ref ::  ((y!=this) ==> packedLeft[y]) );
assert packedLeft[opp];
assert (paramLeftOl[opp] == olpar);
assert (paramLeftLc[opp] == lcpar);
assert packedCount[olpar];
assert packedCount[this];
assert packedRight[this];
assert (paramRightOr[opp] == this);
assert (paramRightRc[opp] == lc + rc + 1);
assert (fracLeft[opp] == 0.5);
assert (fracRight[opp] == 0.5);
assert (fracCount[opp] == 0.5);
assert (paramCountC[opp] == lccc);
assert (count[opp] == lccc);
  
	call updateCountRec(opp, parent[opp], lccc, olpar, this, lcpar, lc + rc + 1);
	}
	else { 
		fracCount[this] := fracCount[this] * 2.0;
    call updateCount(this, lcc, ol, or, lc, rc);
    fracLocalCount[this] := fracCount[this] / 2.0;
    fracCount[this] := fracCount[this] / 2.0;
		call PackParent(this, lc + rc + 1);
		packedParent[this] := true; 
	}  
}

procedure setLeft(this: Ref, l:Ref)
modifies parent, left, count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight, paramCountC, paramLeftOl, paramLeftLc, paramRightRc;
requires this!=null;
requires this!=l;
requires l!=null;
requires right[this]!=parent[this];
requires l!=parent[this];
requires this!=right[this];
requires packedParent[this];
requires fracParent[this] > 0.0;
requires packedParent[l];
requires (forall y:Ref :: packedLeft[y]);
requires (forall y:Ref :: packedRight[y]);
requires (forall y:Ref :: packedParent[y]);
requires (forall y:Ref :: packedCount[y]);
requires (forall y:Ref :: ( fracParent[y] > 0.0 ));
requires fracParent[l] > 0.0;
ensures packedParent[this];
ensures fracParent[this] > 0.0;
 {
// Existentially quantified variable for UnpackParent(l,lc)
var lc : int;
// Existentially quantified variable for UnpackParent(this,lcc)
var lcc : int;
// Existentially quantified variables for UnpackCount(this,lcc)
// The variable rc is also used in the call to updateCountRec()
var ol : Ref;
var or : Ref;
var llc : int;
var rc : int;

call UnpackParent(l, lc);
packedParent[l] := false;
if (parent[l] == null) {
  parent[l] := this;
	call UnpackParent(this, lcc);
	packedParent[this] := false;
	call UnpackCount(this, lcc, null, or, 0, rc);
	packedCount[this] := false;
	fracLeft[this] := fracLeft[this] * 2.0;
	call UnpackLeft(this, null, 0);
	packedLeft[this] := false;

  left[this] := l;
  paramLeftOl[this] := l;
  paramLeftLc[this] := lc;
	call PackLeft(this, l, lc);
	packedLeft[this] := true;

call PackParent(l, lc);
packedParent[l] := true;

assert l!=parent[this];
assert right[this]!=parent[this];
assert packedParent[this] == false;
assert (forall y:Ref :: ( ((y!=this) && (y!=parent[this]) ) ==> packedParent[y]));
assert (forall y:Ref ::  ((y!=this) ==> packedCount[y]));
assert (packedCount[this] == false);
assert (forall y:Ref :: ( fracParent[y] > 0.0 ));
assert (fracParent[this] > 0.0);
assert (parent[this] != null) ==> (fracParent[parent[this]] > 0.0); 
assert (parent[this] != null) ==> packedParent[parent[this]];
assert (parent[this] != null) ==> 
	( ((fracRight[parent[this]] == 0.5) && 
	(paramRightOr[parent[this]] == this) && 
	(paramRightRc[parent[this]] == lcc))
  ||
  	((fracLeft[parent[this]] == 0.5) && 
	(paramLeftOl[parent[this]] == this) && 
	(paramLeftLc[parent[this]] == lcc))
  );
assert (parent[this] == null) ==> ((fracCount[this] == 0.5) && 
			    (paramCountC[this] == lcc) );
assert packedLeft[this];
assert (paramLeftOl[this] == l);
assert (paramLeftLc[this] == lc);
assert packedCount[l];
assert packedCount[right[this]];
assert packedRight[this];
// Need a mechanism to say what each param means. 
// They usually mean the current value of a field.
// In those cases, I need a mechanism to say that.
// And the connections between different params. 
assert (paramRightOr[this] == right[this]);
assert (paramRightRc[this] == rc);
assert (fracLeft[this] == 0.5);
assert (fracRight[this] == 0.5);
assert (fracCount[this] == 0.5);
assert (paramCountC[this] == lcc);
assert (count[this] == lcc);
  
call updateCountRec(this, parent[this], lcc, l, right[this], lc, rc);
call PackParent(l, lc);
}
   
}

