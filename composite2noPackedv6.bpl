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
requires (packedParent[this] == false);
requires (parent[this] == op);
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
requires (parent[this] == null) ==> ((fracCount[this] >= 0.5) && (count[this] == c));

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
ensures (parent[this] == null) ==> ((fracCount[this] >= 0.5) && (count[this] == c));

procedure ConstructComposite(count1 :int, left1 : Ref, right1 : Ref, parent1 : Ref, this: Ref);
	 ensures (count[this] == count1) &&
 	 	 (left[this] == left1) &&
 	 	 (right[this] == right1) &&
 	 	 (parent[this] == parent1); 

procedure updateCount(c:int, ol:Ref, or:Ref, op:Ref, c1:int, c2:int, c3:int, this: Ref)
modifies count, packedCount, packedLeft, packedRight, 
	fracCount, fracLeft, fracRight;
requires this != null;
// TODO whenever the input parameters are exactly what they correspond to
//such as left[op] == left[op] then I don't write them in the translation
requires (op!=null) ==> ( ((packedLeft[op]==false)&& (fracLeft[op]>0.0))  || ((packedRight[op]==false)&& (fracRight[op]>0.0)) );
requires (parent[this] == op);
requires (packedCount[this] == false);
requires (fracCount[this] == 1.0);
requires (count[this] == c);
requires packedLeft[this];
requires (fracLeft[this] >= 0.5);
requires (left[this] == ol);
requires (count[ol] == c1);
requires packedRight[this];
requires (fracRight[this] >= 0.5); 
requires (right[this] == or);
requires (count[or] == c2);
requires (op!=null) ==> ((packedCount[op] == false) && (fracCount[op] > 0.0) && (count[op] == c3));
ensures (fracCount[this] == 1.0);
ensures packedCount[this];
ensures (count[this] == c1 + c2 + 1 ); 
ensures (op!=null) ==> ( ((packedLeft[op]==false)&& (fracLeft[op]>0.0))  || ((packedRight[op]==false)&& (fracRight[op]>0.0)) );
ensures (op!=null) ==> ((packedCount[op] == false) && (fracCount[op] > 0.0) && (count[op] == c3));
ensures (fracLeft[this] >= 0.0) && packedLeft[this] && (fracRight[this] >= 0.0) && packedRight[this];
// TODO I have to look which are the ifCondition ==> expression that are the exact same in
// the pre and postcondition and maybe make a new data structure for them. 
// Each item is one part of the &&, which includes the ifcondition and the right part
// of it, that might include ||.
// Those can be disregarded in the ensures forall.
requires (forall x:Ref :: ((x!=this) && (x!=op) ==>  packedCount[x]));
requires (forall x:Ref :: ( (x!=op) ==> packedLeft[x]));
requires (forall x:Ref :: ( (x!=op) ==> packedRight[x]));

ensures (forall y:Ref :: (packedRight[y] == old(packedRight[y]) ) );
ensures (forall y:Ref :: (packedLeft[y] == old(packedLeft[y]) ) );
ensures (forall y:Ref :: ( (this!=y)  ==> (packedCount[y] == old(packedCount[y])) ) );

ensures (forall y:Ref :: ( (y!=this) ==> (fracRight[y] == old(fracRight[y]) ) ) );
ensures (forall y:Ref :: ( (y!=this) ==> (fracLeft[y] == old(fracLeft[y]) ) ) );
ensures (forall y:Ref :: (fracCount[y] == old(fracCount[y]) ) );
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

procedure updateCountRec(opp: Ref, lcc: int, ol: Ref, or: Ref, lc: int, rc: int, this: Ref)
modifies count, packedCount, packedLeft, packedRight, packedParent,
	fracCount, fracParent, fracLeft, fracRight;
// The requires below has to be added automatically to all procedures.
requires this != null;
requires packedParent[this] == false;
requires (fracParent[this] > 0.0);
requires (parent[this] == opp);
requires (opp != this);
requires  (opp != null) ==>
	(fracParent[opp] > 0.0) && packedParent[opp];
requires (opp != null) && (left[opp] == this) ==>
	((fracLeft[opp] >= 0.5) && 
		packedLeft[opp] &&
	     	(left[opp] == this) && 
             	(count[this] == lcc)
	  );
requires (opp != null) && (right[opp] == this) ==>
          (
	     	(fracRight[opp] >= 0.5) && 
		packedRight[opp] &&
		(right[opp] == this) && 
		(count[this] == lcc)
	  );

requires (opp == null) ==> ((fracCount[this] >= 0.5) && 
			    (count[this] == lcc) &&
			(packedCount[this] == false));

requires packedLeft[this];
requires (fracLeft[this] >= 0.5);
requires (left[this] == ol);
requires (count[left[this]] == lc);

requires packedRight[this];
requires (fracRight[this] >= 0.5);
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
ensures (fracParent[this] > 0.0);
ensures  (opp != null) ==>
	(fracParent[opp] > 0.0) && packedParent[opp];

ensures (forall y:Ref :: (old(fracParent[y]) > 0.0) ==> (fracParent[y] > 0.0));  
ensures (forall y:Ref :: packedParent[y]);
{
assume (forall y:Ref :: (fracRight[y] >= 0.0) );
assume (forall y:Ref :: (fracLeft[y] >= 0.0) );
assume (forall y:Ref :: (fracCount[y] >= 0.0) );
assume (forall y:Ref :: (fracParent[y] >= 0.0) );

if (parent[this] != null) {
// TODO see if I should put a splitFrac here
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
	call UnpackCount(count[opp], left[opp], right[opp], count[left[opp]], count[right[opp]], opp);
	packedCount[opp] := false;
	fracLeft[opp] := fracLeft[opp] + 0.5;
	fracRight[opp] := fracRight[opp] + 0.5;

	if (this == right[parent[this]]) {
		call UnpackRight(this, lcc, parent[opp], opp);
		packedRight[opp] := false;
		if (this != null) { fracCount[this] := fracCount[this] + 0.5; }
  
		fracCount[this] := 0.5 + 0.5;

		call updateCount(lcc, ol, or, opp, lc, rc, count[opp], this);

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

		call updateCountRec(parent[opp], count[opp], left[opp], this, count[left[opp]], lc + rc + 1, opp);

		fracLeft[parent[opp]] := 0.0;		
		fracRight[parent[opp]] := 0.0;
		fracCount[parent[this]] := 0.0; 
		fracLeft[parent[this]] := 0.0;
		fracRight[parent[this]] := 0.0;

	}
	else  { 
		call UnpackLeft(this, lcc, parent[opp], opp);
		packedLeft[opp] := false;
		if (this != null) { fracCount[this] := fracCount[this] + 0.5; }
		fracCount[this] := 0.5 + 0.5;

		call updateCount(lcc, ol, or, opp, lc, rc, count[opp], this);

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
		call updateCountRec(parent[opp], count[opp], this, right[opp], lc + rc + 1, count[right[opp]], opp);
		fracLeft[parent[opp]] := 0.0;
		fracRight[parent[opp]] := 0.0;
		fracCount[parent[this]] := 0.0; 
		fracLeft[parent[this]] := 0.0;
		fracRight[parent[this]] := 0.0;
	} 

}
else { 
	fracCount[this] := 0.5 + 0.5;
  	call updateCount(lcc, ol, or, opp, lc, rc, count[opp], this);

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

procedure setLeft(l:Ref, this: Ref) 
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
ensures fracParent[l] > 0.0;
ensures packedParent[l];
ensures (forall y:Ref :: (old(fracParent[y]) > 0.0) ==> (fracParent[y] > 0.0));
ensures (forall y:Ref ::  packedParent[y]);
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

	call updateCountRec(parent[this], lcc, l, right[this], count[l], count[right[this]], this);	
	fracLeft[parent[this]] := 0.0;
	fracRight[parent[this]] := 0.0;
	fracCount[this] := 0.0; 
	fracLeft[this] := 0.0;
	fracRight[this] := 0.0;
} else {
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
}
   
}

