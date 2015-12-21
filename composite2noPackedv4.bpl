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

//var paramCountC : [Ref]int; paramCountC[this] == count[this]
//var paramLeftOl : [Ref]Ref; paramLeftOl[this] == left[this]
//var paramLeftLc : [Ref]int; paramLeftLc[this] == count[left[this]]
//var paramRightOr : [Ref]Ref; paramRightOr[this] == right[this]
//var paramRightRc : [Ref]int; paramRightRc[this] == count[right[this]]

procedure PackLeft(ol:Ref, lc:int, op:Ref, this:Ref);
requires (packedLeft[this] == false);
requires (left[this] == ol);
requires (parent[this] == op);
requires (left[this] != null) ==> ((fracCount[ol] >= 0.5) && (count[ol] == lc));
requires (left[this] != null) ==> (ol!=this);
requires (left[this] != null) ==> (ol!=op);
requires (left[this] == null) ==> (lc == 0);

procedure UnpackLeft(ol:Ref, lc:int, op:Ref, this:Ref);
requires packedLeft[this];
requires (fracLeft[this] > 0.0);
ensures (left[this] == ol);
ensures (parent[this] == op);
ensures (left[this] == null) ==> (lc == 0);
ensures (left[this] != null) ==> ((fracCount[ol] == old(fracCount[ol]) + 0.5) && (count[ol] == lc));
ensures (left[this] != null) ==> (ol!=this);
ensures (left[this] != null) ==> (ol!=op);

procedure PackRight(or:Ref, rc:int, op:Ref, this:Ref);
requires (packedRight[this] == false);
requires (right[this] == or);
requires (parent[this] == op);
requires (right[this] == or);
requires (right[this] != null) ==> ((fracCount[or] >= 0.5) && (count[or] == rc));
requires (right[this] != null) ==> (or!=this);
requires (right[this] != null) ==> (or!=op);
requires (right[this] == null) ==> (rc == 0);

procedure UnpackRight(or:Ref, rc:int, op:Ref, this:Ref);
requires packedRight[this];
requires (fracRight[this] > 0.0);
ensures (right[this] == or);
ensures (parent[this] == op);
ensures (right[this] == null) ==> (rc == 0);
ensures (right[this] != null) ==> ((fracCount[or] == old(fracCount[or]) + 0.5) && (count[or] == rc));
ensures (right[this] != null) ==> (or!=this);
ensures (right[this] != null) ==> (or!=op);

procedure PackCount(c:int, ol: Ref, or:Ref, lc:int, rc:int, this:Ref);
requires (packedCount[this] == false);
requires (count[this] == c);
requires (fracLeft[this] >= 0.5);
requires (fracRight[this] >= 0.5);
requires (right[this] == or);
requires (count[or] == rc);
requires (left[this] == ol);
requires (count[ol] == lc);
requires (c == lc + rc + 1);

procedure UnpackCount(c:int, ol: Ref, or:Ref, lc:int, rc:int, this:Ref);
requires packedCount[this];
requires (fracCount[this] > 0.0);
ensures (count[this] == c);
ensures (fracLeft[this] == old(fracLeft[this]) + 0.5);
ensures (fracRight[this] == old(fracRight[this]) + 0.5);
ensures (right[this] == or);
ensures (count[or] == rc);
ensures (left[this] == ol);
ensures (count[ol] == lc);
ensures (c == lc + rc + 1);

procedure PackParent(op:Ref, c:int, this:Ref);
requires (packedParent[this] == false);
requires (fracCount[this] >= 0.5);
requires (count[this] == c);
requires (parent[this] != this);
requires  (parent[this] != null) ==>
	(fracParent[op] > 0.0) ;
requires (parent[this] != null) && (left[op] == this) ==>
	((fracLeft[op] >= 0.5) && 
	     	(left[op] == this) && 
             	(count[this] == c)
	  );
requires (parent[this] != null) && (right[op] == this) ==>
          (
	     	(fracRight[op] >= 0.5) && 
		(right[op] == this) && 
		(count[this] == c)
	  );
requires (parent[this] == null) ==> (fracCount[this] >= 0.5);
requires (parent[this] == null) ==> packedCount[this];
requires (parent[this] == op);


procedure UnpackParent(op:Ref, c:int, this:Ref);
requires packedParent[this];
requires (fracParent[this] > 0.0);
ensures (parent[this] == op);
ensures (parent[this] != this);
ensures packedCount[this];
ensures (count[this] == c);
ensures (fracCount[this] == old(fracCount[this]) + 0.5);
// Here I might need to put
// fracParent[] == old(fracParent[]) + 0.0001)
// I definitely need to add something to old() because
// there might already be a frac before this unpackParent is 
// called.
ensures  (parent[this] != null) ==>
	(fracParent[op] == old(fracParent[op]) + 0.0001) ;
ensures (parent[this] != null) && (left[op] == this) ==>
	((fracLeft[op] == old(fracLeft[op]) + 0.5) && 
	     	(left[op] == this) && 
             	(count[this] == c)
	  );
ensures (parent[this] != null) && (right[op] == this) ==>
          (
	     	(fracRight[op] == old(fracRight[op]) + 0.5) && 
		(right[op] == this) && 
		(count[this] == c)
	  );
ensures (parent[this]==null) ==> (fracCount[this] == old(fracCount[this]) + 0.5);
ensures (parent[this]==null) ==> (count[this] == c);

//---start of methods

//TODO might need to change this to look like the
//other constructors
procedure ConstructComposite(this:Ref);
ensures (count[this] == 1);
ensures	(left[this] == null);
ensures	(right[this] == null);
ensures	(parent[this] == null);

procedure updateCount(this: Ref, c:int, ol:Ref, or:Ref, op:Ref, c1:int, c2:int, c3:int)
modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;
requires this != null;
requires packedLeft[this];
requires (fracLeft[this] == 0.5);
requires (left[this] == ol);
requires (count[ol] == c1);
requires packedRight[this];
requires (fracRight[this] == 0.5); 
requires (right[this] == or);
requires (count[or] == c2);
requires (packedCount[this] == false);
requires (fracCount[this] == 1.0);
requires (count[this] == c);
requires (parent[this] == op);
//needs to be put in by the programmer
requires ((packedLeft[op]==false) && (fracLeft[op] > 0.0) && (count[left[op]] == c)) || 
	((packedRight[op]==false) && (fracRight[op] > 0.0) && (count[right[op]] == c)) ||
	(op==null);
requires (op!=null) ==> ((packedCount[op] == false) && (fracCount[op] > 0.0) && (count[op] == c3));
requires (forall y:Ref :: ( ( (y!=this) && (y!=op) ) ==> (packedCount[y] ) ) );
//We need to add these two requires forall to make it consistent with the requires above.
requires (forall y:Ref :: ( (y!=op) ==> packedRight[y]));
requires (forall y:Ref :: ( (y!=op) ==> packedLeft[y]));
ensures (fracCount[this] == 1.0);
ensures packedCount[this];
ensures (count[this] == c1 + c2 + 1 );  
// Only write here about the global variables in the modifies clause.
//ensures (forall y:Ref :: (fracRight[y] == old(fracRight[y]) ) );
//ensures (forall y:Ref :: (fracLeft[y] == old(fracLeft[y]) ) );
ensures (forall y:Ref :: (packedRight[y] == old(packedRight[y]) ) );
ensures (forall y:Ref :: (packedLeft[y] == old(packedLeft[y]) ) );
ensures (forall y:Ref :: (fracCount[y] == old(fracCount[y]) ) );
ensures (forall y:Ref :: ((y!=this) ==> (count[y] == old(count[y]) ) ) );
ensures (forall y:Ref :: ( (this!=y)  ==> (packedCount[y] == old(packedCount[y])) ) );
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

//This assume can also be written like an axiom.
//We need to know when to call that axiom.
//Otherwise it has to be written in all procedures
//and it has to mention even fracs from previous files.
//I might add that fracs are also <= 1.0.
assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );
call UnpackLeft(ol, c1, op, this);
packedLeft[this] := false;
if (ol != null) { fracCount[ol] := fracCount[ol] + 0.5; }

if (left[this] != null) {
	call UnpackCount(c1, ol1, or1, lc1, rc1, ol);
	packedCount[ol] := false; 
	fracLeft[ol] := fracLeft[ol] + 0.5; 
	fracRight[ol] := fracRight[ol] + 0.5; 
   	newc := newc + count[left[this]];
	call PackCount(c1, ol1, or1, lc1, rc1, ol);
	packedCount[ol]:=true;
	fracLeft[ol] := fracLeft[ol] - 0.5;
	fracRight[ol] := fracRight[ol] - 0.5;
}
call PackLeft(ol, c1, op, this);
packedLeft[this] := true;
if (ol!=null) { fracCount[ol] := fracCount[ol] - 0.5; }
   
call UnpackRight(or, c2, op, this);
packedRight[this] := false;
if (or!=null) { fracCount[or] := fracCount[or] + 0.5; }
    
if (right[this] != null) {
	call UnpackCount(c2, ol2, or2, lc2, rc2, or);
	packedCount[or] := false;
	fracLeft[or] := fracLeft[or] + 0.5; 
	fracRight[or] := fracRight[or] + 0.5;
  	newc := newc + count[right[this]]; 
  	call PackCount(c2, ol2, or2, lc2, rc2, or);
	packedCount[or] := true;
	fracLeft[or] := fracLeft[or] - 0.5;
	fracRight[or] := fracRight[or] - 0.5;
}

call PackRight(or, c2, op, this);
packedRight[this] := true;
if (or != null) { fracCount[or] := fracCount[or] - 0.5; }
    
count[this] := newc; 
//TODO: We don't need to do this anymore.
//We update the corresponding paramCount for that field
//whenever we update a field.
//Here it is difficult because this is the phase where we need to use what we know and 
//instantiate the exists with the right values.
//Here we need to use the fraction to right(this).
call PackCount(newc, ol, or, c1, c2, this);
packedCount[this]:=true; 
fracLeft[this] := fracLeft[this] - 0.5;
fracRight[this] := fracRight[this] - 0.5;
}

procedure updateCountRec(this: Ref, opp: Ref, lcc: int, ol: Ref, or: Ref, lc: int, rc: int)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires (this != null);
requires packedParent[this] == false;
requires (fracParent[this] > 0.0);
requires (parent[this] == opp);
requires (opp != this);
requires  (opp != null) ==>
	(fracParent[opp] > 0.0) ;
requires (opp != null) && (left[opp] == this) ==>
	((fracLeft[opp] >= 0.5) && 
	     	(left[opp] == this) && 
             	(count[this] == lcc)
	  );
requires (opp != null) && (right[opp] == this) ==>
          (
	     	(fracRight[opp] >= 0.5) && 
		(right[opp] == this) && 
		(count[this] == lcc)
	  );

requires (opp == null) ==> ((fracCount[this] == 0.5) && 
			    (count[this] == lcc) );

requires packedLeft[this];
requires (fracLeft[this] == 0.5);
requires (left[this] == ol);
requires (count[left[this]] == lc);

requires (fracRight[this] == 0.5);
requires packedRight[this];
requires (right[this] == or);
requires (count[right[this]] == rc);

requires (packedCount[this] == false);
requires (fracCount[this] == 0.5);
requires (count[this] == lcc);

requires (forall y:Ref :: ((y!=this) ==> packedParent[y]));
requires (forall y:Ref :: ((y!=this) ==> packedCount[y]));
requires (forall y:Ref ::  packedLeft[y] ) ;
requires (forall y:Ref ::  packedRight[y] ) ;

ensures packedParent[this];  
ensures (forall y:Ref :: (old(fracParent[y]) > 0.0) ==> (fracParent[y] > 0.0) );  
ensures (forall y:Ref :: packedParent[y] );
{

// Existential variables for UnpackCount(opp, lccc)
var oll : Ref;
var orr : Ref;
var llc : int;
var rrc : int;

// Existential variables used in the parameters of call updateCountRec()
var oppp : Ref;

assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );

if (parent[this] != null) {

	call UnpackParent(parent[opp], count[opp], opp);
	packedParent[opp] := false;
 
	// Instantiate orr==this and rrc==lcc;
	call UnpackCount(count[opp], oll, this, llc, lcc, opp);
	packedCount[opp] := false;

	assert ((this == right[parent[this]]) || (this == left[parent[this]]) );
	if (this == right[parent[this]]) {
	
		call UnpackRight(this, lcc, parent[opp], opp);
		packedRight[opp] := false;
  
		call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);

		call PackParent(parent[this], lc + rc + 1, this);
		packedParent[this] := true;
	
		call PackRight(this, lc + rc + 1, parent[opp], opp);
		packedRight[opp] := true;
		call updateCountRec(opp, parent[opp], count[opp], left[opp], this, count[left[opp]], lc + rc + 1);
	}
	else if (this == left[parent[this]]) { 
		//fracLeft[opp] := 2.0 * fracLeft[opp];
	
		call UnpackLeft(this, lcc, parent[opp], opp);
		packedLeft[opp] := false;
  
		call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);

		call PackParent(parent[this], lc + rc + 1, this);
		packedParent[this] := true;
	
		call PackLeft(this, lc + rc + 1, parent[opp], opp);
		packedLeft[opp] := true;
		call updateCountRec(opp, parent[opp], count[opp], this, right[opp], count[left[opp]], lc + rc + 1);
	}
//TODO I don't know if I need to add a final else here 
//that has in its body something like "assume false".
}
else { 
  	call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);

	call PackParent(parent[this], lc + rc + 1, this);
	packedParent[this] := true; 
}  
}

procedure setLeft(this: Ref, l:Ref)
modifies parent, left, count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
requires this!=null;
requires this!=l;
requires l!=null;
requires left[this]!=parent[this];
requires l!=parent[this];
requires this!=left[this];
requires packedParent[this];
requires fracParent[this] > 0.0;
requires fracParent[l] > 0.0;
requires packedParent[l];
requires (forall y:Ref :: packedLeft[y]);
requires (forall y:Ref :: packedRight[y]);
requires (forall y:Ref :: packedParent[y]);
requires (forall y:Ref :: packedCount[y]);
ensures packedParent[this];
ensures fracParent[this] > 0.0;
 {
// Existentially quantified variable for UnpackParent(this,lcc)
var lcc : int;
// Existentially quantified variables for UnpackCount(this,lcc)
// The variable rc is also used in the call to updateCountRec()
var or : Ref;

assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );

call UnpackParent(parent[l], count[l], l);
packedParent[l] := false;

if (parent[l] == null) {
	parent[l] := this;
	call UnpackParent(parent[this], lcc, this);
	packedParent[this] := false;
	call UnpackCount(lcc, null, or, 0, count[right[this]], this);
	packedCount[this] := false;
  
  	call UnpackLeft(null, 0, parent[this], this);
	packedLeft[this] := false;

  	left[this] := l;
	count[left[this]] := count[l];
	call PackLeft(l, count[l], parent[this], this);
	packedLeft[this] := true;

	call PackParent(parent[l], count[l], l);
  	packedParent[l] := true;

	call updateCountRec(this, parent[this], lcc, l, right[this], count[l], count[right[this]]);
}
   
}

