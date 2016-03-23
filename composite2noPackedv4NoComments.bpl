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
ensures (left[this] != null) ==> ((fracCount[ol] >= 0.5) && (count[ol] == lc));
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
ensures (right[this] != null) ==> ((fracCount[or] >= 0.5) && (count[or] == rc));
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
ensures (fracLeft[this] >= 0.5);
ensures (fracRight[this] >= 0.5);
ensures (right[this] == or);
ensures (count[or] == rc);
ensures (left[this] == ol);
ensures (count[ol] == lc);
ensures (c == lc + rc + 1);

procedure PackParent(op:Ref, c:int, this:Ref);
requires (parent[this] == op);
requires (packedParent[this] == false);
requires (fracCount[this] >= 0.5);
requires (count[this] == c);
requires (parent[this] != this);
requires  (parent[this] != null) ==>
	(fracParent[op] > 0.0) ;
requires ((op != null) && (left[op] == this)) ==>
	(
		(fracLeft[op] >= 0.5) && 
	     	(left[op] == this) && 
             	(count[this] == c)
	  );
requires ((op != null) && (right[op] == this)) ==>
          (
	     	(fracRight[op] >= 0.5) && 
		(right[op] == this) && 
		(count[this] == c)
	  );
requires (parent[this] == null) ==> (fracCount[this] >= 0.5);
requires (parent[this] == null) ==> packedCount[this];


procedure UnpackParent(op:Ref, c:int, this:Ref);
requires packedParent[this];
requires (fracParent[this] > 0.0);
ensures (parent[this] == op);
ensures (parent[this] != this);
ensures packedCount[this];
ensures (fracCount[this] >= 0.5);
ensures (count[this] == c);
ensures (parent[this] != null) && (left[op] == this) ==>
	(
		(fracLeft[op] >= 0.5) && 
	     	(left[op] == this) && 
             	(count[this] == c)
	  );
ensures (parent[this] != null) && (right[op] == this) ==>
          (
		(fracRight[op] >= 0.5) && 
		(right[op] == this) && 
		(count[this] == c)
	  );
ensures (parent[this] == null) ==> (fracCount[this] >= 0.5);
ensures (parent[this]==null) ==> (count[this] == c);

procedure ConstructComposite(count1 :int, left1 : Ref, right1 : Ref, parent1 : Ref, this: Ref);
	 ensures (count[this] == count1) &&
 	 	 (left[this] == left1) &&
 	 	 (right[this] == right1) &&
 	 	 (parent[this] == parent1); 

procedure updateCount(this: Ref, c:int, ol:Ref, or:Ref, op:Ref, c1:int, c2:int, c3:int)
modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;
requires this != null;
requires packedLeft[this];
requires (fracLeft[this] >= 0.5);
requires (left[this] == ol);
requires (count[ol] == c1);
requires packedRight[this];
requires (fracRight[this] >= 0.5); 
requires (right[this] == or);
requires (count[or] == c2);
requires (packedCount[this] == false);
requires (fracCount[this] == 1.0);
requires (count[this] == c);
requires (parent[this] == op);
requires (op!=null) ==> ((packedCount[op] == false) && (fracCount[op] > 0.0) && (count[op] == c3));
requires (forall x:Ref :: ((x!=this) && (x!=op) ==>  packedCount[x]));
ensures (fracCount[this] == 1.0);
ensures packedCount[this];
ensures (count[this] == c1 + c2 + 1 );  

ensures (forall y:Ref :: ( (y!=this) ==> (fracRight[y] == old(fracRight[y]) ) ) );
ensures (forall y:Ref :: ( (y!=this) ==> (fracLeft[y] == old(fracLeft[y]) ) ) );
ensures (forall y:Ref :: (packedRight[y] == old(packedRight[y]) ) );
ensures (forall y:Ref :: (packedLeft[y] == old(packedLeft[y]) ) );
ensures (forall y:Ref :: (fracCount[y] == old(fracCount[y]) ) );
ensures (forall y:Ref :: ((y!=this) ==> (count[y] == old(count[y]) ) ) );
ensures (forall y:Ref :: ( (this!=y)  ==> (packedCount[y] == old(packedCount[y])) ) );
{
var newc : int;
var ol1: Ref;
var or1:Ref;
var lc1:int;
var rc1:int;

var ol2: Ref;
var or2:Ref;
var lc2:int;
var rc2:int;

newc := 1;

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
call PackCount(newc, ol, or, c1, c2, this);
packedCount[this] := true; 
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

requires (opp == null) ==> ((fracCount[this] >= 0.5) && 
			    (count[this] == lcc) );

requires packedLeft[this];
requires (fracLeft[this] >= 0.5);
requires (left[this] == ol);
requires (count[left[this]] == lc);

requires (fracRight[this] >= 0.5);
requires packedRight[this];
requires (right[this] == or);
requires (count[right[this]] == rc);

requires (packedCount[this] == false);
requires (fracCount[this] >= 0.5);
requires (count[this] == lcc);

requires (forall y:Ref :: ((y!=this) ==> packedParent[y]));
requires (forall y:Ref :: ((y!=this) ==> packedCount[y]));
requires (forall y:Ref ::  packedLeft[y] ) ;
requires (forall y:Ref ::  packedRight[y] ) ;

ensures packedParent[this];  
ensures (forall y:Ref :: (old(fracParent[y]) > 0.0) ==> (fracParent[y] > 0.0) );  
ensures (forall y:Ref :: packedParent[y] );
{
var oll : Ref;
var orr : Ref;
var llc : int;
var rrc : int;
var oppp : Ref;

assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );

if (parent[this] != null) {

	call UnpackParent(parent[opp], count[opp], opp);
	packedParent[opp] := false;
	fracCount[opp] := fracCount[opp] + 0.5;
	if (parent[opp] != null) { 
		fracParent[parent[opp]] := fracParent[parent[opp]] + 0.001; 
	}
	if ((parent[opp] != null) && (left[parent[opp]] == opp)) {
		fracLeft[parent[opp]] := fracLeft[parent[opp]] + 0.5; 
	}
	if ((parent[opp] != null) && (right[parent[opp]] == opp)) { 
		fracRight[parent[opp]] := fracRight[parent[opp]] + 0.5; 
	}
	if (parent[opp] == null) { fracCount[opp] := fracCount[opp] + 0.5; }

	call UnpackCount(count[opp], oll, this, llc, lcc, opp);
	packedCount[opp] := false;
	fracLeft[opp] := fracLeft[opp] + 0.5;
	fracRight[opp] := fracRight[opp] + 0.5;

	assert ((this == right[parent[this]]) || (this == left[parent[this]]) );
	if (this == right[parent[this]]) {
		fracRight[opp] := 0.5 + 0.5;

		call UnpackRight(this, lcc, parent[opp], opp);
		packedRight[opp] := false;
		if (this != null) { fracCount[this] := fracCount[this] + 0.5; }
  
		fracCount[this] := 0.5 + 0.5;

		call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);


		fracLeft[this] := fracLeft[this] - 0.5;
		fracRight[this] := fracRight[this] - 0.5;
		if (opp!=null) { fracCount[opp] := fracCount[opp] / 2.0; }

		fracCount[this] := 1.0;

		call PackParent(parent[this], lc + rc + 1, this);
		packedParent[this] := true;
		fracCount[this] := fracCount[this] - 0.5;
		if (opp!=null) { fracParent[opp] := fracParent[opp] / 2.0; }
		if ((opp != null) && (left[opp] == this)) {
			fracLeft[opp] := fracLeft[opp] - 0.5;
		}
		if ((opp != null) && (right[opp] == this)) {
			fracRight[opp] := fracRight[opp] - 0.5;
		}
		if (opp == null) {
			fracCount[this] := fracCount[this] - 0.5;
		}
	
		call PackRight(this, lc + rc + 1, parent[opp], opp);
		packedRight[opp] := true;
		if (this != null) { fracCount[this] := fracCount[this] - 0.5;}

		call updateCountRec(opp, parent[opp], count[opp], left[opp], this, count[left[opp]], lc + rc + 1);
		//TODO I need to add another fraction manipulation statement here, related to 
		// the unpacked(parent...)
		// TODO make sure this translation is the translation I want for 
		// Composite.java, with all the right fraction manipulation statements.
		// In the translation, I have the if probably because of the "unpacked" before which is considered an identifier.
		// If the predicate is unpacked in the precondition, it means I still have a fraction to that predicate, but 
		// the actual property might not hold. But I do still hold a fraction to the predicate.
		// So I need to subtract that fraction in the fraction manipulation statements, just like any other fraction.
		if (parent[opp] != null) {
			 fracParent[parent[opp]] := fracParent[parent[opp]] / 2.0; 
		} 
		if ((parent[opp] != null) && (left[parent[opp]] == opp)) {
			fracLeft[parent[opp]] := fracLeft[parent[opp]] - 0.5;
		}
		if ((parent[opp] != null) && (right[parent[opp]] == opp)) { 
			fracRight[parent[opp]] := fracRight[parent[opp]] - 0.5;
		}
		if (parent[opp] == null) { 
			fracCount[parent[this]] := fracCount[parent[this]] - 0.5; 
		}
		fracLeft[parent[this]] := fracLeft[parent[this]] - 0.5;
		fracRight[parent[this]] := fracRight[parent[this]] - 0.5;
		
		fracParent[parent[this]] := fracParent[parent[this]] + 0.001;
	}
	else if (this == left[parent[this]]) { 
		fracLeft[opp] := 0.5 + 0.5;
		call UnpackLeft(this, lcc, parent[opp], opp);
		packedLeft[opp] := false;
		if (this != null) { fracCount[this] := fracCount[this] + 0.5; }
		// TODO do I need this now. Why?
		fracCount[this] := 0.5 + 0.5;
  
		call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);

		fracLeft[this] := fracLeft[this] - 0.5;
		fracRight[this] := fracRight[this] - 0.5;
		if (opp!=null) { fracCount[opp] := fracCount[opp] / 2.0; }
		fracCount[this] := 1.0;

		call PackParent(parent[this], lc + rc + 1, this);
		packedParent[this] := true;
		fracCount[this] := fracCount[this] - 0.5;
		if (opp!=null) { fracParent[opp] := fracParent[opp] / 2.0; }
		if ((opp != null) && (left[opp] == this)) {
			fracLeft[opp] := fracLeft[opp] - 0.5;
		}
		if ((opp != null) && (right[opp] == this)) {
			fracRight[opp] := fracRight[opp] - 0.5;
		}
		if (opp == null) {
			fracCount[this] := fracCount[this] - 0.5;
		}
	
		call PackLeft(this, lc + rc + 1, parent[opp], opp);
		packedLeft[opp] := true;
		if (this != null) { fracCount[this] := fracCount[this] - 0.5;}
		call updateCountRec(opp, parent[opp], count[opp], this, right[opp], count[left[opp]], lc + rc + 1);
		if (parent[opp] != null) { 
			fracParent[parent[opp]] := fracParent[parent[opp]] / 2.0; 
		} 

		if ((parent[opp] != null) && (left[parent[opp]] == opp)) {
			fracLeft[parent[opp]] := fracLeft[parent[opp]] - 0.5;
		}
		if ((parent[opp] != null) && (right[parent[opp]] == opp)) { 
			fracRight[parent[opp]] := fracRight[parent[opp]] - 0.5;
		}
		if (parent[opp] == null) { 
			fracCount[parent[this]] := fracCount[parent[this]] - 0.5; 
		}
		fracLeft[parent[this]] := fracLeft[parent[this]] - 0.5;
		fracRight[parent[this]] := fracRight[parent[this]] - 0.5;
		
		fracParent[parent[this]] := fracParent[parent[this]] + 0.001;
	}
}
else { 
	fracCount[this] := 0.5 + 0.5;
  	call updateCount(this, lcc, ol, or, opp, lc, rc, count[opp]);
	fracCount[this] := fracCount[this] - 1.0;
	fracLeft[this] := fracLeft[this] - 0.5;
	fracRight[this] := fracRight[this] - 0.5;
	if (opp != null) {
		fracCount[opp] := fracCount[opp] / 2.0;
	}
	fracCount[this] := fracCount[this] + 1.0;

	call PackParent(parent[this], lc + rc + 1, this);
	packedParent[this] := true; 
	fracCount[this] := fracCount[this] - 0.5;
	if (opp!=null) { fracParent[opp] := fracParent[opp] / 2.0; }
	if ((opp != null) && (left[opp] == this)) {
		fracLeft[opp] := fracLeft[opp] - 0.5;
	}
	if ((opp != null) && (right[opp] == this)) {
		fracRight[opp] := fracRight[opp] - 0.5;
	}
	if (opp == null) {
		fracCount[this] := fracCount[this] - 0.5;
	}
}  
}

procedure setLeft(this: Ref, l:Ref) 
// Here I might need to add more because of transitivity,
// the methods that are called from inside.
modifies parent, left, count, packedCount, packedLeft, packedParent, packedRight,
	fracCount, fracParent, fracLeft, fracRight;
requires this != null;
requires this!=l;
requires l!=null;
requires left[this]!=parent[this];
requires l!=parent[this];
requires l!=right[this];
requires this!=left[this];
requires packedParent[this];
requires fracParent[this] > 0.0;
requires fracParent[l] > 0.0;
requires packedParent[l];

requires (forall y:Ref :: packedLeft[y]);
requires (forall y:Ref :: packedCount[y]);
requires (forall y:Ref ::  packedRight[y] ) ;
requires (forall y:Ref ::  packedParent[y] ) ;
ensures packedParent[this];
ensures fracParent[this] > 0.0;
 {
var lcc : int;
var or : Ref;

assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );

call UnpackParent(parent[l], count[l], l);
packedParent[l] := false;
fracCount[l] := fracCount[l] + 0.5;
if (parent[l] != null) { 
	fracParent[parent[l]] := fracParent[parent[l]] + 0.001; 
}
if ((parent[l] != null) && (left[parent[l]] == l)) { 
	fracLeft[parent[l]] := fracLeft[parent[l]] + 0.5; 
}
if ((parent[l] != null) && (right[parent[l]] == l)) {
	fracRight[parent[l]] := fracRight[parent[l]] + 0.5; 
}
if (parent[l] == null) { fracCount[l] := fracCount[l] + 0.5; }

if (parent[l] == null) {
	parent[l] := this;
	call UnpackParent(parent[this], lcc, this);
	packedParent[this] := false;
	fracCount[this] := fracCount[this] + 0.5;
	if (parent[this] != null) { 
		fracParent[parent[this]] := fracParent[parent[this]] + 0.001; 
	}
	if ((parent[this] != null) && (left[parent[this]] == this)) { 
		fracLeft[parent[this]] := fracLeft[parent[this]] + 0.5; 
	}
	if ((parent[this] != null) && (right[parent[this]] == this)) {
		fracRight[parent[this]] := fracRight[parent[this]] + 0.5; 
	}
	if (parent[this] == null) { fracCount[this] := fracCount[this] + 0.5; }
	call UnpackCount(lcc, null, or, 0, count[right[this]], this);
	packedCount[this] := false;
	fracLeft[this] := fracLeft[this] + 0.5;
	fracRight[this] := fracRight[this] + 0.5;

	fracLeft[this] := 0.5 + 0.5;
  
  call UnpackLeft(null, 0, parent[this], this);
	packedLeft[this] := false;

  	left[this] := l;
	count[left[this]] := count[l];
  
	call PackLeft(l, count[l], parent[this], this);
	packedLeft[this] := true;
	if (l != null) {
		fracCount[l] := fracCount[l] + 0.5;
	}

	call PackParent(parent[l], count[l], l);
  	packedParent[l] := true;
	fracCount[l] := fracCount[l] - 0.5;

	if (parent[l] != null) { 
		fracParent[parent[l]] := fracParent[parent[l]] / 2.0; 
	}

	if ((parent[l] != null) && (left[parent[l]] == l)) {
		fracLeft[parent[l]] := fracLeft[parent[l]] - 0.5;
	}

	if ((parent[l] != null) && (right[parent[l]] == l)) {
		fracRight[parent[l]] := fracRight[parent[l]] - 0.5;
	}

	if (parent[l] == null) {
		fracCount[l] := fracCount[l] - 0.5;
	}

	call updateCountRec(this, parent[this], lcc, l, right[this], count[l], count[right[this]]);
	if (parent[this] != null) { 
		fracParent[parent[this]] := fracParent[parent[this]] / 2.0; } 
	if ((parent[this] != null) && (left[parent[this]] == this)) {
		fracLeft[parent[this]] := fracLeft[parent[this]] - 0.5;
	}
	if ((parent[this] != null) && (right[parent[this]] == this)) { 
		fracRight[parent[this]] := fracRight[parent[this]] - 0.5;
	}
	if (parent[this] == null) { 
		fracCount[this] := fracCount[this] - 0.5; 
	}
	fracLeft[this] := fracLeft[this] - 0.5;
	fracRight[this] := fracRight[this] - 0.5;
	
	fracParent[this] := fracParent[this] + 0.001;
}
   
}

