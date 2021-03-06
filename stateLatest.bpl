//intcell.bpl
type Ref;
const null: Ref;

var value: [Ref]int;
var divider : [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedBasicIntCell: [Ref] bool;
var fracBasicIntCell: [Ref] real;

var packedIntCellMany : [Ref] bool;
var fracIntCellMany : [Ref]real;

var packedIntCellFew : [Ref] bool;
var fracIntCellFew : [Ref]real;

function modulo(x:int, y:int) returns (int);
axiom (forall x:int, y:int :: {modulo(x,y)} 
    ((0 <= x) &&(0 < y) ==> (0 <= modulo(x,y) ) && (modulo(x,y) < y) )
    &&
    ((0 <= x) &&(y < 0) ==> (0 <= modulo(x,y) ) && (modulo(x,y) < -y) )
    &&
    ((x <= 0) &&(0 < y) ==> (-y <= modulo(x,y) ) && (modulo(x,y) <= 0) )
    &&
    ((x <= 0) &&(y < 0) ==> (y <= modulo(x,y) ) && (modulo(x,y) <= 0) )
   ); 

procedure PackBasicIntCell(a: int, v:int, this:Ref);
requires (packedBasicIntCell[this]==false);
requires (value[this] == v);
requires (divider[this] == a);

procedure UnpackBasicIntCell(a: int, v:int, this:Ref);
requires packedBasicIntCell[this];
requires fracBasicIntCell[this] > 0.0;
requires (value[this] == v);
requires (divider[this] == a);

procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false);
requires (value[this] == v);
requires (divider[this] == a);
requires ( (v - int(v/a)*a )==0);

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
requires (value[this] == v);
ensures (divider[this] == a);
ensures	 ( (v - int(v/a)*a )==0);

procedure PackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires (packedIntCellMany[this]==false);
requires (value[this] == val);
requires (divider[this] == divi);
requires (quot >= 10);

procedure UnpackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires packedIntCellMany[this];
requires fracIntCellMany[this] > 0.0;
requires (value[this] == val);
requires (divider[this] == divi);
ensures (quot >= 10);

procedure PackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires (packedIntCellFew[this]==false);
requires (value[this] == v);
requires (divider[this] == divi);
requires (quot <= 4);

procedure UnpackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires packedIntCellFew[this];
requires fracIntCellFew[this] > 0.0;
requires (value[this] == v);
requires (divider[this] == divi);
ensures (quot <= 4);

procedure ConstructIntCell(divider1: int, value1: int, this: Ref)
modifies divider, value;
ensures (value[this] == value1);
ensures (divider[this] == divider1);
{
	value[this] := value1;
	divider[this] := divider1;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r := value[this];
}

//----------------------
//statelive.bpl

var cell : [Ref]Ref;
var instanceof : [Ref]int;

var packedStateMultipleOf3StateLive: [Ref]bool;
var fracStateMultipleOf3StateLive: [Ref]real;

var packedStateMultipleOf2StateLive: [Ref]bool;
var fracStateMultipleOf2StateLive: [Ref]real;

procedure PackStateMultipleOf3StateLive(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateLive[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 21);

procedure UnpackStateMultipleOf3StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLive[this];
requires fracStateMultipleOf3StateLive[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 21);

procedure PackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 4);

procedure UnpackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLive[this];
requires fracStateMultipleOf2StateLive[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 4);

procedure ConstructStateLive(this:Ref)
modifies cell, divider, value;
//ensures (forall y:Ref :: ( (y!=this) ==> (cell[y] == old(cell[y]) ) ) );
{	
	var temp:Ref;
	call ConstructIntCell(1, 0, temp);
	call ConstructStateLive2(temp, cell[this]);
}

procedure ConstructStateLive2(c:Ref, this:Ref)
modifies cell;
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive, 
         packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep, packedStateMultipleOf3StateLimbo
         , fracStateMultipleOf3StateLimbo, divider, packedMultipleOf, fracMultipleOf,
         packedStateContextMultiple3;
requires (packedStateContextMultiple3[context]==false);
requires (fracStateContextMultiple3[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (packedStateContextMultiple3[context]==true);
ensures (fracStateContextMultiple3[context] > 0.0);
ensures packedStateLimbo[context];
ensures	(fracStateLimbo[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple3[x] == old(packedStateContextMultiple3[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(33, num*33, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(33, num*33, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=33;

call ConstructStateLimbo2(i1, r);
packedStateMultipleOf3StateLimbo[r] := false;
call PackStateMultipleOf3StateLimbo(i1, r);
packedStateMultipleOf3StateLimbo[r] := true;
fracStateMultipleOf3StateLimbo[r] := 1.0;

instanceof[r] := 2;
call setState3(r, context);
}

procedure computeResult2StateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , divider, packedMultipleOf, fracMultipleOf, packedStateMultipleOf2StateLive,
         fracStateMultipleOf2StateSleep, packedStateMultipleOf2StateSleep,
         packedStateContextMultiple2;
requires (packedStateContextMultiple2[context] == false);
requires (fracStateContextMultiple2[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (packedStateContextMultiple2[context] == true);
ensures (fracStateContextMultiple2[context] > 0.0);
ensures packedStateSleep[context];
ensures	(fracStateSleep[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple2[x] == old(packedStateContextMultiple2[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(16, num*16, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(16, num*16, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=16;

call ConstructStateSleep2(i1, r);
packedStateMultipleOf2StateSleep[r] := false;
call PackStateMultipleOf2StateSleep(i1, r);
packedStateMultipleOf2StateSleep[r] := true;
fracStateMultipleOf2StateSleep[r] := 1.0;

instanceof[r] := 3;

// StateLike s = new StateSleep()[];
call setState2(r, context);
}

procedure checkMod3StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateLive[this];
requires (fracStateMultipleOf3StateLive[this] > 0.0);
ensures packedStateMultipleOf3StateLive[this];
requires (fracStateMultipleOf3StateLive[this] > 0.0);
{
var temp : int;
call temp := getValueInt(cell[this]);
b:= (modulo(temp, 3) == 0);
}

procedure checkMod2StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLive[this];
requires (fracStateMultipleOf2StateLive[this] > 0.0);
ensures packedStateMultipleOf2StateLive[this];
requires (fracStateMultipleOf2StateLive[this] > 0.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b:= (modulo(temp, 2) == 0);
}

//--------------------------------------------
//statelimbo.bpl

var packedStateMultipleOf3StateLimbo: [Ref]bool;
var fracStateMultipleOf3StateLimbo: [Ref]real;

var packedStateMultipleOf2StateLimbo: [Ref]bool;
var fracStateMultipleOf2StateLimbo: [Ref]real;

procedure PackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 33);

procedure UnpackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLimbo[this];
requires fracStateMultipleOf3StateLimbo[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 33);

procedure PackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 14);

procedure UnpackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLimbo[this];
requires fracStateMultipleOf2StateLimbo[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 14);

procedure ConstructStateLimbo(this:Ref)
modifies cell, divider, value;
{	
	var temp:Ref;
	call ConstructIntCell(1, 0, temp);
	call ConstructStateLimbo2(temp, cell[this]);
}

procedure ConstructStateLimbo2(c:Ref, this:Ref)
modifies cell;
ensures cell[this] == c;
{	
	cell[this] := c;
}


procedure computeResultStateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
           , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
           , divider, packedMultipleOf, fracMultipleOf, packedStateMultipleOf3StateSleep,
           fracStateMultipleOf3StateSleep, packedStateContextMultiple3;
requires (packedStateContextMultiple3[context]==false);
requires (fracStateContextMultiple3[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (packedStateContextMultiple3[context]==true);
ensures (fracStateContextMultiple3[context] > 0.0);
ensures packedStateSleep[context];
ensures	(fracStateSleep[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==> packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==> packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple3[x] == old(packedStateContextMultiple3[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(15, num*15, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(15, num*15, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=15;

call ConstructStateSleep2(i1, r);
packedStateMultipleOf3StateSleep[r] := false;
call PackStateMultipleOf3StateSleep(i1, r);
packedStateMultipleOf3StateSleep[r] := true;
fracStateMultipleOf3StateSleep[r] := 1.0;

instanceof[r] := 3;

// StateLike s = new StateSleep()[];
call setState3(r, context);
}

procedure computeResult2StateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , divider, packedMultipleOf, fracMultipleOf, packedStateMultipleOf2StateLimbo,
         packedStateMultipleOf2StateLive, fracStateMultipleOf2StateLive,
         packedStateContextMultiple2;
requires (fracStateContextMultiple2[context] > 0.0);
requires (packedStateContextMultiple2[context]==false);
requires (fracStateContextMultiple2[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (packedStateContextMultiple2[context]==true);
ensures (fracStateContextMultiple2[context] > 0.0);
ensures packedStateLive[context];
ensures	(fracStateLive[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple2[x] == old(packedStateContextMultiple2[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(4, num*4, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(4, num*4, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=4;

call ConstructStateLive2(i1, r);
packedStateMultipleOf2StateLive[r] := false;
call PackStateMultipleOf2StateLive(i1, r);
packedStateMultipleOf2StateLive[r] := true;
fracStateMultipleOf2StateLive[r] := 1.0;

instanceof[r] := 1;

// StateLike s = new StateLive()[];
call setState2(r, context);
}

procedure checkMod3StateLimbo(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateLimbo[this];
requires (fracStateMultipleOf3StateLimbo[this] > 0.0);
ensures packedStateMultipleOf3StateLimbo[this];
ensures	(fracStateMultipleOf3StateLimbo[this] > 0.0);
{
var temp : int;
call temp := getValueInt(cell[this]);
b := (modulo(temp, 3) == 0);
}

procedure checkMod2StateLimbo(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLimbo[this];
requires (fracStateMultipleOf2StateLimbo[this] > 0.0);
ensures packedStateMultipleOf2StateLimbo[this];
ensures	(fracStateMultipleOf2StateLimbo[this] > 0.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b := (modulo(temp, 2) == 0);
}

//-----------------------------------------
//statesleep.bpl

var packedStateMultipleOf3StateSleep: [Ref]bool;
var fracStateMultipleOf3StateSleep: [Ref]real;

var packedStateMultipleOf2StateSleep: [Ref]bool;
var fracStateMultipleOf2StateSleep: [Ref]real;

procedure PackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 15);

procedure UnpackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf3StateSleep[this];
requires fracStateMultipleOf3StateSleep[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 15);

procedure PackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 16);

procedure UnpackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf2StateSleep[this];
requires fracStateMultipleOf2StateSleep[this] > 0.0;
requires (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 16);

procedure ConstructStateSleep(this:Ref)
modifies cell, divider, value;
{	
	var temp:Ref;
	call ConstructIntCell(1, 0, temp);
	call ConstructStateSleep2(temp, cell[this]);
}

procedure ConstructStateSleep2(c:Ref, this:Ref)
modifies cell;
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateSleep(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
          , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
          , divider, packedMultipleOf, fracMultipleOf, packedStateMultipleOf3StateLive,
          fracStateMultipleOf3StateLive, packedStateContextMultiple3;
requires (packedStateContextMultiple3[context]==false);
requires (fracStateContextMultiple3[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (packedStateContextMultiple3[context]==true);
ensures (fracStateContextMultiple3[context] > 0.0);
ensures packedStateLive[context];
ensures	(fracStateLive[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple3[x] == old(packedStateContextMultiple3[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(21, num*21, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(21, num*21, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=21;

call ConstructStateLive2(i1, r);
packedStateMultipleOf3StateLive[r] := false;
call PackStateMultipleOf3StateLive(i1, r);
packedStateMultipleOf3StateLive[r] := true;
fracStateMultipleOf3StateLive[r] := 1.0;

instanceof[r] := 1;
call setState3(r, context);
}

procedure computeResult2StateSleep(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
          , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
          , divider, packedMultipleOf, fracMultipleOf, packedStateMultipleOf2StateSleep,
          fracStateMultipleOf2StateLimbo, packedStateMultipleOf2StateLimbo
          ,packedStateContextMultiple2;
requires (packedStateContextMultiple2[context]==false);
requires (fracStateContextMultiple2[context] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x]));
ensures (packedStateContextMultiple2[context]==true);
ensures (fracStateContextMultiple2[context] > 0.0);
ensures packedStateLimbo[context];
ensures	(fracStateLimbo[context] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=context) ==> (packedStateContextMultiple2[x] == old(packedStateContextMultiple2[x]))) ); 
{
var i1:Ref;

call ConstructIntCell(14, num*14, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(14, num*14, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=14;

call ConstructStateLimbo2(i1, r);
packedStateMultipleOf2StateLimbo[r] := false;
call PackStateMultipleOf2StateLimbo(i1, r);
packedStateMultipleOf2StateLimbo[r] := true;
fracStateMultipleOf2StateLimbo[r] := 1.0;

instanceof[r] := 2;

// StateLike s = new StateLimbo()[];
call setState2(r, context);
}

procedure checkMod3StateSleep(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateSleep[this];
requires (fracStateMultipleOf3StateSleep[this] > 0.0);
ensures packedStateMultipleOf3StateSleep[this];
ensures	(fracStateMultipleOf3StateSleep[this] > 0.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b := (modulo(temp, 3) == 0);
}

procedure checkMod2StateSleep(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateSleep[this];
requires (fracStateMultipleOf2StateSleep[this] > 0.0);
ensures packedStateMultipleOf2StateSleep[this];
ensures	(fracStateMultipleOf2StateSleep[this] > 0.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b := (modulo(temp, 2) == 0);
}

//-------------------------------
//statecontext.bpl

var myState: [Ref]Ref;

var packedStateLive :[Ref]bool;
var fracStateLive :[Ref]real;

var packedStateLimbo :[Ref]bool;
var fracStateLimbo :[Ref]real;

var packedStateSleep :[Ref]bool;
var fracStateSleep :[Ref]real;

var packedStateContextMultiple2 : [Ref]bool;
var fracStateContextMultiple2 : [Ref]real;

var packedStateContextMultiple3 : [Ref]bool;
var fracStateContextMultiple3 : [Ref]real;

procedure PackStateContextMultiple2(m:Ref, this:Ref);
requires (packedStateContextMultiple2[this] == false);
requires (myState[this] == m);
requires (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[m] > 0.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[m] > 0.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[m] > 0.0);

procedure UnpackStateContextMultiple2(m:Ref, this:Ref);
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
requires (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[m] > 0.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[m] > 0.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[m] > 0.0);

procedure PackStateContextMultiple3(m:Ref, this:Ref);
requires (packedStateContextMultiple3[this] == false);
requires (myState[this] == m);
requires (instanceof[m] == 1) ==> (fracStateMultipleOf3StateLive[m] > 0.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf3StateLimbo[m] > 0.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf3StateSleep[m] > 0.0);

procedure UnpackStateContextMultiple3(m:Ref, this:Ref);
requires packedStateContextMultiple3[this];
requires fracStateContextMultiple3[this] > 0.0;
requires (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf3StateLive[m] > 0.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf3StateLimbo[m] > 0.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf3StateSleep[m] > 0.0);
	
procedure ConstructStateContext(mysta:Ref, this:Ref) 
modifies myState;
ensures myState[this] == mysta;
{ 
  myState[this] := mysta;
 // instanceof[myState[this]] := instanceof[mysta];
} 

procedure setState2(newState:Ref, this:Ref) 
modifies myState, instanceof, packedStateLive, fracStateLive
       , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep, 
       packedStateContextMultiple2;
requires (packedStateContextMultiple2[this] == false);
requires fracStateContextMultiple2[this] > 0.0;
requires (instanceof[newState] == 1) ==> (fracStateMultipleOf2StateLive[newState] > 0.0);
requires (instanceof[newState] == 2) ==> (fracStateMultipleOf2StateLimbo[newState] > 0.0);
requires (instanceof[newState] == 3) ==> (fracStateMultipleOf2StateSleep[newState] > 0.0);

requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 

ensures myState[this] == newState;
ensures instanceof[myState[this]] == instanceof[newState];

ensures ((old(instanceof[newState]) == 1) ==> ( packedStateLive[this] && (fracStateLive[this] > 0.0)));
ensures	((old(instanceof[newState]) == 2) ==> ( packedStateLimbo[this] && (fracStateLimbo[this] > 0.0)));
ensures	((old(instanceof[newState]) == 3) ==> ( packedStateSleep[this] && (fracStateSleep[this] > 0.0)));
ensures packedStateContextMultiple2[this];
ensures (forall y:Ref :: (y!=myState[this]) ==> (instanceof[y] == old(instanceof[y]))); 
ensures (forall y:Ref :: (y!=this) ==> (myState[y] == old(myState[y]))); 
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=this) ==> (packedStateContextMultiple2[x] == old(packedStateContextMultiple2[x]))) ); 
{ 
	myState[this] := newState; 
	instanceof[myState[this]] := instanceof[newState];
  if (instanceof[newState] == 1 ) {
     packedStateLive[this] := true;
     fracStateLive[this] := 0.001;
  } else
  if (instanceof[newState] == 2 ) {
     packedStateLimbo[this] := true;
     fracStateLimbo[this] := 0.001;
  } else
  if (instanceof[newState] == 3 ) {
     packedStateSleep[this] := true;
     fracStateSleep[this] := 0.001;
  } else {
    assume false;
  }

  call PackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := true;
} 


procedure setState3(newState:Ref, this:Ref) 
modifies myState, instanceof, packedStateLive, fracStateLive
       , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep, 
       packedStateContextMultiple3;
requires (packedStateContextMultiple3[this] == false);
requires fracStateContextMultiple3[this] > 0.0;
requires (instanceof[newState] == 1) ==> (fracStateMultipleOf3StateLive[newState] > 0.0);
requires (instanceof[newState] == 2) ==> (fracStateMultipleOf3StateLimbo[newState] > 0.0);
requires (instanceof[newState] == 3) ==> (fracStateMultipleOf3StateSleep[newState] > 0.0);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures myState[this] == newState;
ensures instanceof[myState[this]] == instanceof[newState];

ensures ((old(instanceof[newState]) == 1) ==> ( packedStateLive[this] && (fracStateLive[this] > 0.0)));
ensures	((old(instanceof[newState]) == 2) ==> ( packedStateLimbo[this] && (fracStateLimbo[this] > 0.0)));
ensures	((old(instanceof[newState]) == 3) ==> ( packedStateSleep[this] && (fracStateSleep[this] > 0.0)));
ensures packedStateContextMultiple3[this];
ensures (forall y:Ref :: (y!=myState[this]) ==> (instanceof[y] == old(instanceof[y]))); 
ensures (forall y:Ref :: (y!=this) ==> (myState[y] == old(myState[y]))); 
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ((x!=this) ==> (packedStateContextMultiple3[x] == old(packedStateContextMultiple3[x]))) ); 
{ 
	myState[this] := newState; 
	instanceof[myState[this]] := instanceof[newState];
  if (instanceof[newState] == 1 ) {
     packedStateLive[this] := true;
     fracStateLive[this] := 0.001;
  } else
  if (instanceof[newState] == 2 ) {
     packedStateLimbo[this] := true;
     fracStateLimbo[this] := 0.001;
  } else
  if (instanceof[newState] == 3 ) {
     packedStateSleep[this] := true;
     fracStateSleep[this] := 0.001;
  } else {
    assume false;
  }
  call PackStateContextMultiple3(myState[this], this);
  packedStateContextMultiple3[this] := true;
     
} 

procedure computeResultSC(num: int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive,
        packedStateMultipleOf3StateLive , packedStateLimbo, fracStateLimbo
        , packedStateSleep, fracStateSleep, divider, packedMultipleOf, fracMultipleOf,
        packedStateContextMultiple3, packedStateMultipleOf3StateLimbo, 
        packedStateMultipleOf3StateSleep, fracStateMultipleOf3StateLimbo,
        fracStateMultipleOf3StateSleep, fracStateMultipleOf3StateLive;
requires packedStateContextMultiple3[this]==false;
requires fracStateContextMultiple3[this] > 0.0;
requires (instanceof[myState[this]] == 1) ==> (
      packedStateMultipleOf3StateLive[myState[this]] &&
      (fracStateMultipleOf3StateLive[myState[this]] > 0.0)
);
requires (instanceof[myState[this]] == 2) ==> (
      packedStateMultipleOf3StateLimbo[myState[this]] &&
      (fracStateMultipleOf3StateLimbo[myState[this]] > 0.0)
);
requires (instanceof[myState[this]] == 3) ==> (
      packedStateMultipleOf3StateSleep[myState[this]] &&
      (fracStateMultipleOf3StateSleep[myState[this]] > 0.0)
);
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
requires (forall  x:Ref :: ((x!=this) ==> packedStateContextMultiple3[x])); 
//requires (forall x:Ref :: ( packedMultipleOf[x]));
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] > 0.0;
ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
//ensures (forall x:Ref :: ( packedMultipleOf[x]));
{
if (instanceof[myState[this]] == 1) {
	call r := computeResultStateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2)  {
	call r := computeResultStateLimbo(this, num, myState[this]);
} else if (instanceof[myState[this]] == 3)  {
	call r := computeResultStateSleep(this, num, myState[this]);
} 
else {
  // We cannot be in this else and we 
  // express this like below.
  assume false;
}
}

procedure computeResult2SC(num: int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , packedStateContextMultiple2, divider, packedMultipleOf, fracMultipleOf,
         packedStateMultipleOf2StateLimbo, fracStateMultipleOf2StateLimbo,
         packedStateMultipleOf2StateSleep, fracStateMultipleOf2StateSleep,
          packedStateMultipleOf2StateLive, fracStateMultipleOf2StateLive;
requires packedStateContextMultiple2[this]==false;
requires fracStateContextMultiple2[this] > 0.0;
requires (instanceof[myState[this]] == 1) ==> (
      packedStateMultipleOf2StateLive[myState[this]] &&
      (fracStateMultipleOf2StateLive[myState[this]] > 0.0)
);
requires (instanceof[myState[this]] == 2) ==> (
      packedStateMultipleOf2StateLimbo[myState[this]] &&
      (fracStateMultipleOf2StateLimbo[myState[this]] > 0.0)
);
requires (instanceof[myState[this]] == 3) ==> (
      packedStateMultipleOf2StateSleep[myState[this]] &&
      (fracStateMultipleOf2StateSleep[myState[this]] > 0.0)
);
//requires (forall x:Ref :: ( packedMultipleOf[x]));
requires (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x]==2)==>  packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x]==3)==>  packedStateMultipleOf2StateSleep[x])); 
requires (forall  x:Ref :: ((x!=this) ==> packedStateContextMultiple2[x])); 
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this] > 0.0;

ensures (forall  x:Ref :: ((instanceof[x]==1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==2)==> packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x]==3)==> packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ( packedStateContextMultiple2[x])); 
//ensures (forall x:Ref :: ( packedMultipleOf[x]));
{
if (instanceof[myState[this]] == 1) {
	call r := computeResult2StateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call r := computeResult2StateLimbo(this, num, myState[this]);
} else if (instanceof[myState[this]] == 3) {
	call r := computeResult2StateSleep(this, num, myState[this]);
} else {
  assume false;
}
}

procedure stateContextCheckMultiplicity3(this:Ref) returns (b:bool) 
modifies packedStateContextMultiple3;
requires packedStateContextMultiple3[this];
requires fracStateContextMultiple3[this] > 0.0;
requires (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf3StateSleep[x])); 
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] > 0.0; 
ensures (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
{ 
   call UnpackStateContextMultiple3(myState[this], this);
  packedStateContextMultiple3[this] := false;
if (instanceof[myState[this]] == 1) {
	call b := checkMod3StateLive(myState[this]);
  call PackStateContextMultiple3(myState[this], this);
  packedStateContextMultiple3[this] := true;
} else if (instanceof[myState[this]] == 2) {
	call b := checkMod3StateLimbo(myState[this]);
  call PackStateContextMultiple3(myState[this], this);
  packedStateContextMultiple3[this] := true;
} else if (instanceof[myState[this]] == 3){
	call b := checkMod3StateSleep(myState[this]);
  call PackStateContextMultiple3(myState[this], this);
  packedStateContextMultiple3[this] := true;
} else {
  // This means we cannot end up in this else.
  assume false;
}
} 

procedure stateContextCheckMultiplicity2(this:Ref) returns (b:bool) 
modifies packedStateContextMultiple2;
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
requires (forall  x:Ref :: ( packedStateContextMultiple2[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf2StateSleep[x])); 
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this] > 0.0;
ensures (forall  x:Ref :: ( packedStateContextMultiple2[x])); 
{ 
if (instanceof[myState[this]] == 1) {
  call UnpackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := false;
	call b := checkMod2StateLive(myState[this]);
  call PackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := true;
} else if (instanceof[myState[this]] == 2) {
  call UnpackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := false;
	call b := checkMod2StateLimbo(myState[this]);
  call PackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := true;
} else if (instanceof[myState[this]] == 3) {
  call UnpackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := false;
	call b := checkMod2StateSleep(myState[this]);
  call PackStateContextMultiple2(myState[this], this);
  packedStateContextMultiple2[this] := true;
} else {
  // This means we cannot end up in this else.
  assume false;
}
} 

//--------------------------------
//stateclient.bpl

var scon: [Ref]Ref;

var packedStateClientMultiple2:[Ref]bool;
var fracStateClientMultiple2:[Ref]real;

var packedStateClientMultiple3:[Ref]bool;
var fracStateClientMultiple3:[Ref]real;

procedure PackStateClientMultiple2(s:Ref, this:Ref);
requires (packedStateClientMultiple2[this] == false);
requires (scon[this] == s);
requires (fracStateContextMultiple2[s] > 0.0);

procedure UnpackStateClientMultiple2(s:Ref, this:Ref);
requires packedStateClientMultiple2[this];
requires fracStateClientMultiple2[this] > 0.0;
requires (scon[this] == s);
ensures (fracStateContextMultiple2[s] > 0.0);

procedure PackStateClientMultiple3(s:Ref, this:Ref);
requires (packedStateClientMultiple3[this] == false);
requires (scon[this] == s);
requires (fracStateContextMultiple3[s] > 0.0);

procedure UnpackStateClientMultiple3(s:Ref, this:Ref);
requires packedStateClientMultiple3[this];
requires fracStateClientMultiple3[this] > 0.0;
requires (scon[this] == s);
ensures (fracStateContextMultiple3[s] > 0.0);

procedure ConstructStateClient(sco:Ref, this:Ref)
modifies scon;
ensures (scon[this] == sco);
{
 scon[this] := sco; 
}

procedure stateClientCheckMultiplicity3(this:Ref) returns (r:bool)
modifies packedStateContextMultiple3, packedStateClientMultiple3;
requires packedStateClientMultiple3[this];
requires (fracStateClientMultiple3[this] > 0.0);
requires (forall  x:Ref :: ( packedStateClientMultiple3[x]));
requires (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf3StateSleep[x])); 
requires (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
ensures packedStateClientMultiple3[this];
ensures (fracStateClientMultiple3[this] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf3StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf3StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf3StateSleep[x])); 
ensures (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
ensures (forall  x:Ref :: ( packedStateClientMultiple3[x])); 
{
  call UnpackStateClientMultiple3(scon[this], this);
  packedStateClientMultiple3[this] := false;
  call r:= stateContextCheckMultiplicity3(scon[this]);
  call PackStateClientMultiple3(scon[this], this);
  packedStateClientMultiple3[this] := true;
}
 
procedure stateClientCheckMultiplicity2(this:Ref) returns (r:bool)
modifies packedStateContextMultiple2, packedStateClientMultiple2;
requires packedStateClientMultiple2[this];
requires (fracStateClientMultiple2[this] > 0.0);
requires (forall  x:Ref :: ( packedStateClientMultiple2[x]));
requires (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf2StateSleep[x])); 
requires (forall  x:Ref :: ( packedStateContextMultiple2[x]));
ensures packedStateClientMultiple2[this];
ensures (fracStateClientMultiple2[this] > 0.0);
ensures (forall  x:Ref :: ((instanceof[x] == 1)==> packedStateMultipleOf2StateLive[x])); 
ensures (forall  x:Ref :: ((instanceof[x] == 2)==> packedStateMultipleOf2StateLimbo[x])); 
ensures (forall  x:Ref :: ((instanceof[x] == 3)==> packedStateMultipleOf2StateSleep[x])); 
ensures (forall  x:Ref :: ( packedStateContextMultiple2[x])); 
ensures (forall  x:Ref :: ( packedStateClientMultiple2[x]));
{
  call UnpackStateClientMultiple2(scon[this], this);
  packedStateClientMultiple2[this] := false;
  call r := stateContextCheckMultiplicity2(scon[this]);
  call PackStateClientMultiple2(scon[this], this);
  packedStateClientMultiple2[this] := true;
}
 
procedure main1(this:Ref)
modifies cell, packedMultipleOf, fracMultipleOf, instanceof,
        myState, divider, value, fracStateClientMultiple3,
        packedStateClientMultiple3, packedStateMultipleOf3StateLive,
        fracStateMultipleOf3StateLive, packedStateContextMultiple3,
        fracStateContextMultiple3,   
        packedStateLive, fracStateLive,
        packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep,
        packedStateMultipleOf3StateLimbo, 
        packedStateMultipleOf3StateSleep, 
        fracStateMultipleOf3StateLimbo, fracStateMultipleOf3StateSleep,
        fracStateMultipleOf3StateLive, scon;
requires (forall x:Ref :: ( packedMultipleOf[x]));
requires (forall  x:Ref :: ( packedStateMultipleOf3StateLive[x])); 
requires (forall  x:Ref :: ( packedStateMultipleOf3StateLimbo[x])); 
requires (forall  x:Ref :: ( packedStateMultipleOf3StateSleep[x])); 
requires (forall  x:Ref :: ( packedStateContextMultiple3[x])); 
requires (forall  x:Ref :: ( packedStateClientMultiple3[x]));
{
var i1, i2 : Ref;
var st1, st2 : Ref;
var scontext1, scontext2 : Ref;
var sclient1, sclient2, sclient3, sclient4 : Ref;
var tempRef : Ref;
var tempBool : bool;

assume (i1 != i2);
assume (st1 != st2);
assume (sclient1 != sclient2);
assume (sclient3 != sclient4);
assume (scontext1 != scontext2);

call ConstructIntCell(21, 21, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(21, 21, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=21;

call ConstructStateLive2(i1, st1);
packedStateMultipleOf3StateLive[st1] := false;
call PackStateMultipleOf3StateLive(i1, st1);
packedStateMultipleOf3StateLive[st1] := true;
fracStateMultipleOf3StateLive[st1] := 1.0;

instanceof[st1] := 1;
call ConstructStateContext(st1, scontext1);
packedStateContextMultiple3[scontext1] := false;
call PackStateContextMultiple3(st1, scontext1);
packedStateContextMultiple3[scontext1] := true;
fracStateContextMultiple3[scontext1] := 1.0;

call ConstructStateClient(scontext1, sclient1);
packedStateClientMultiple3[sclient1] := false;
call PackStateClientMultiple3(scontext1, sclient1);
packedStateClientMultiple3[sclient1] := true;
fracStateClientMultiple3[sclient1] := 1.0;

call ConstructStateClient(scontext1, sclient2);
packedStateClientMultiple3[sclient2] := false;
call PackStateClientMultiple3(scontext1, sclient2);
packedStateClientMultiple3[sclient2] := true;
fracStateClientMultiple3[sclient2] := 1.0;

call UnpackStateContextMultiple3(myState[scontext1], scontext1);
packedStateContextMultiple3[scontext1] := false;
call tempRef := computeResultSC(1, scontext1);
call tempBool := stateClientCheckMultiplicity3(sclient1); 

call UnpackStateContextMultiple3(myState[scontext1], scontext1);
packedStateContextMultiple3[scontext1] := false;
call tempRef := computeResultSC(2, scontext1); 
call tempBool := stateClientCheckMultiplicity3(sclient2); 

call UnpackStateContextMultiple3(myState[scontext1], scontext1);
packedStateContextMultiple3[scontext1] := false;
call tempRef := computeResultSC(3, scontext1); 
call tempBool := stateClientCheckMultiplicity3(sclient1); 		
}

procedure main2(this:Ref)
modifies cell, packedMultipleOf, fracMultipleOf, instanceof,
        myState, divider, value, 
        packedStateMultipleOf2StateLive,
        fracStateMultipleOf2StateLive, packedStateContextMultiple2,
        fracStateContextMultiple2, packedStateClientMultiple2,
        fracStateClientMultiple2, packedStateLive, fracStateLive,
        packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep,
        packedStateMultipleOf2StateLimbo,
        packedStateMultipleOf2StateSleep,
        fracStateMultipleOf2StateLimbo, fracStateMultipleOf2StateSleep, scon;
requires (forall x:Ref :: ( packedMultipleOf[x]));
requires (forall  x:Ref :: ( packedStateMultipleOf2StateLive[x])); 
requires (forall  x:Ref :: ( packedStateMultipleOf2StateLimbo[x])); 
requires (forall  x:Ref :: ( packedStateMultipleOf2StateSleep[x])); 
requires (forall  x:Ref :: ( packedStateContextMultiple2[x])); 
requires (forall  x:Ref :: ( packedStateClientMultiple2[x]));
{
var i1, i2 : Ref;
var st1, st2 : Ref;
var scontext1, scontext2 : Ref;
var sclient1, sclient2, sclient3, sclient4 : Ref;
var tempRef : Ref;
var tempBool : bool;

assume (i1 != i2);
assume (st1 != st2);
assume (sclient1 != sclient2);
assume (sclient3 != sclient4);
assume (scontext1 != scontext2);

call ConstructIntCell(4, 4, i2);
packedMultipleOf[i2] := false;
call PackMultipleOf(4, 4, i2);
packedMultipleOf[i2] := true;
fracMultipleOf[i2] := 1.0;
divider[i2] := 4;

call ConstructStateLive2(i2, st2);
packedStateMultipleOf2StateLive[st2] := false;
call PackStateMultipleOf2StateLive(i2, st2);
packedStateMultipleOf2StateLive[st2] := true;
fracStateMultipleOf2StateLive[st2] := 1.0;

instanceof[st2] := 1;

call ConstructStateContext(st2, scontext2);
packedStateContextMultiple2[scontext2] := false;
call PackStateContextMultiple2(st2, scontext2);
packedStateContextMultiple2[scontext2] := true;
fracStateContextMultiple2[scontext2] := 1.0;

call ConstructStateClient(scontext2, sclient3);
packedStateClientMultiple2[sclient3] := false;
call PackStateClientMultiple2(scontext2, sclient3);
packedStateClientMultiple2[sclient3] := true;
fracStateClientMultiple2[sclient3] := 1.0;

call ConstructStateClient(scontext2, sclient4);
packedStateClientMultiple2[sclient4] := false;
call PackStateClientMultiple2(scontext2, sclient4);
packedStateClientMultiple2[sclient4] := true;
fracStateClientMultiple2[sclient4] := 1.0;

call UnpackStateContextMultiple2(myState[scontext2], scontext2);
packedStateContextMultiple2[scontext2] := false;

call tempRef := computeResult2SC(1, scontext2);
call tempBool := stateClientCheckMultiplicity2(sclient3); 
call UnpackStateContextMultiple2(myState[scontext2], scontext2);
packedStateContextMultiple2[scontext2] := false;
call tempRef := computeResult2SC(2, scontext2); 
call tempBool := stateClientCheckMultiplicity2(sclient4); 
call UnpackStateContextMultiple2(myState[scontext2], scontext2);
packedStateContextMultiple2[scontext2] := false;
call tempRef := computeResult2SC(3, scontext2); 
call tempBool := stateClientCheckMultiplicity2(sclient3); 			
}

