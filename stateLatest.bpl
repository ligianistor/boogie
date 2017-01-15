type Ref;
const null: Ref;

var value: [Ref]int;
var divider : [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedBasicIntCell: [Ref] bool;
var fracBasicIntCell: [Ref] real;

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

// TODO need to be able to go from BasicIntCell to one of
// the more complex predicates and back.
procedure PackBasicIntCell(a: int, v:int, this:Ref);
requires (packedBasicIntCell[this]==false);
requires (value[this] == v);
requires (divider[this] == a);

procedure UnpackBasicIntCell(a: int, v:int, this:Ref);
requires packedBasicIntCell[this];
requires fracBasicIntCell[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);

procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false);
requires (value[this] == v);
requires (divider[this] == a);
requires (modulo(v,a) == 0); 

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);
ensures	(modulo(v,a) == 0); 

procedure ConstructIntCell(x: int, this: Ref);
ensures (value[this] == x);

procedure setValue(x: int, divi:int, this: Ref) 
modifies value, divider,
      packedMultipleOf, fracMultipleOf;
//requires (fracBasicIntCell[this] == 1.0); 
requires (fracMultipleOf[this] == 1.0);
requires packedMultipleOf[this];
requires (divider[this] == 21) || (divider[this] == 16) ||
	(divider[this] == 15) || (divider[this] == 14) ||
	(divider[this] == 33) || (divider[this] == 4);
ensures (divider[this] == divi);
ensures (fracMultipleOf[this] == 1.0);
ensures packedMultipleOf[this];
{
	value[this] := x;
  divider[this] := divi;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r:=value[this];
}

//----------------------

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
requires (divider[cell[this]] == 15);

procedure UnpackStateMultipleOf3StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLive[this];
requires fracStateMultipleOf3StateLive[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 15);

procedure PackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 14);

procedure UnpackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLive[this];
requires fracStateMultipleOf2StateLive[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 14);

procedure ConstructStateLive(this:Ref)
modifies cell;
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateLive2(temp, cell[this]);
}

procedure ConstructStateLive2(c:Ref, this:Ref)
modifies cell;
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive, packedStateMultipleOf3StateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 1;
requires (packedStateMultipleOf3StateLive[this]==false);
requires (fracStateMultipleOf3StateLive[this] > 0.0);
requires packedStateContextMultiple3[context];
requires (fracStateContextMultiple3[context] > 0.0);
ensures packedStateMultipleOf3StateLive[this];
ensures	(fracStateMultipleOf3StateLive[this] > 0.0);
ensures packedStateLimbo[context];
ensures	(fracStateLimbo[context] > 0.0);
{
var s : Ref;
call ConstructStateLimbo(s);
instanceof[s]:=2;
// StateLike s = new StateLimbo()[];
call setState(s, context);
call setValue(num*15, 15, cell[this]);
call PackStateMultipleOf3StateLive(cell[this], this);
packedStateMultipleOf3StateLive[this] := true;
r := cell[this];
}

procedure computeResult2StateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 1;
requires (packedStateMultipleOf2StateLive[this]==false);
requires (fracStateMultipleOf2StateLive[this] > 0.0);
requires packedStateContextMultiple2[context];
requires (fracStateContextMultiple2[context] > 0.0);
ensures packedStateMultipleOf2StateLive[this];
ensures (fracStateMultipleOf2StateLive[this] > 0.0);
ensures packedStateSleep[context];
ensures	(fracStateSleep[context] > 0.0);
{
var s : Ref;
call ConstructStateSleep(s);
instanceof[s] := 3;
// StateLike s = new StateSleep()[];
call setState(s, context);
call setValue(num*14, 14, cell[this]);
r:=cell[this];
}

procedure checkMod3StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateLive[this];
requires (fracStateMultipleOf3StateLive[this] > 0.0);
ensures packedStateMultipleOf3StateLive[this];
requires (fracStateMultipleOf3StateLive[this] > 0.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
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

var packedStateMultipleOf3StateLimbo: [Ref]bool;
var fracStateMultipleOf3StateLimbo: [Ref]real;

var packedStateMultipleOf2StateLimbo: [Ref]bool;
var fracStateMultipleOf2StateLimbo: [Ref]real;

procedure PackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 21);

procedure UnpackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLimbo[this];
requires fracStateMultipleOf3StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 21);

procedure PackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 16);

procedure UnpackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLimbo[this];
requires fracStateMultipleOf2StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 16);

procedure ConstructStateLimbo(this:Ref)
modifies cell;
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateLimbo2(temp, cell[this]);
}

procedure ConstructStateLimbo2(c:Ref, this:Ref)
modifies cell;
//TODO this should be a predicate
ensures cell[this] == c;
{	
	cell[this] := c;
}


procedure computeResultStateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
           , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
           , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 2;
requires packedStateMultipleOf3StateLimbo[this];
requires (fracStateMultipleOf3StateLimbo[this] > 0.0);
requires packedStateContextMultiple3[context];
requires (fracStateContextMultiple3[context] > 0.0);
ensures packedStateMultipleOf3StateLimbo[this];
ensures	(fracStateMultipleOf3StateLimbo[this] > 0.0);
ensures packedStateSleep[context];
ensures	(fracStateSleep[context] > 0.0);
{
var s : Ref;
call ConstructStateSleep(s);
instanceof[s]:=3;
// StateLike s = new StateSleep()[];
call setState(s, context);
call setValue(num*21,21, cell[this]);
r := cell[this];
}

procedure computeResult2StateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 2;
requires packedStateMultipleOf2StateLimbo[this];
requires (fracStateMultipleOf2StateLimbo[this] > 0.0);
requires packedStateContextMultiple2[context];
requires (fracStateContextMultiple2[context] > 0.0);
ensures packedStateMultipleOf2StateLimbo[this];
ensures	(fracStateMultipleOf2StateLimbo[this] > 0.0);
ensures packedStateLive[context];
ensures	(fracStateLive[context] > 0.0);
{
var s : Ref;
call ConstructStateLive(s);
instanceof[s]:=1;
// StateLike s = new StateLive()[];
call setState(s, context);
call setValue(num*16, 16, cell[this]);
r:=cell[this];
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

var packedStateMultipleOf3StateSleep: [Ref]bool;
var fracStateMultipleOf3StateSleep: [Ref]real;

var packedStateMultipleOf2StateSleep: [Ref]bool;
var fracStateMultipleOf2StateSleep: [Ref]real;

procedure PackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 33);

procedure UnpackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf3StateSleep[this];
requires fracStateMultipleOf3StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 33);

procedure PackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf[c] > 0.0);
requires (divider[cell[this]] == 4);

procedure UnpackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf2StateSleep[this];
requires fracStateMultipleOf2StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf[c] > 0.0);
ensures (divider[cell[this]] == 4);

procedure ConstructStateSleep(this:Ref)
modifies cell;
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
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
          , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 3;
requires packedStateMultipleOf3StateSleep[this];
requires (fracStateMultipleOf3StateSleep[this] > 0.0);
requires packedStateContextMultiple3[context];
requires (fracStateContextMultiple3[context] > 0.0);
ensures packedStateMultipleOf3StateSleep[this];
ensures	(fracStateMultipleOf3StateSleep[this] > 0.0);
ensures packedStateLive[context];
ensures	(fracStateLive[context] > 0.0);
{
var s : Ref;
call ConstructStateLive(s);
instanceof[s]:=1;
// StateLike s = new StateLive()[];
call setValue(num*33, 33, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateSleep(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
          , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
          , divider, packedMultipleOf, fracMultipleOf;
requires instanceof[this] == 3;
requires packedStateMultipleOf2StateSleep[this];
requires (fracStateMultipleOf2StateSleep[this] > 0.0);
requires packedStateContextMultiple2[context];
requires (fracStateContextMultiple2[context] > 0.0);
ensures packedStateMultipleOf2StateSleep[this];
ensures	(fracStateMultipleOf2StateSleep[this] > 0.0);
ensures packedStateLimbo[context];
ensures	(fracStateLimbo[context] > 0.0);
{
var s : Ref;
call ConstructStateLimbo(s);
instanceof[s]:=2;
// StateLike s = new StateLimbo()[];
call setState(s, context);
call setValue(num*14, 14, cell[this]);
r:=cell[this];
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

var myState: [Ref]Ref;

var packedBasicFieldsContext : [Ref]bool;
var fracBasicFieldsContext : [Ref]real;

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
requires (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] > 0.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] > 0.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] > 0.0);

procedure UnpackStateContextMultiple2(m:Ref, this:Ref);
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
ensures (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] > 0.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] > 0.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] > 0.0);

procedure PackStateContextMultiple3(m:Ref, this:Ref);
requires (packedStateContextMultiple3[this] == false);
requires (myState[this] == m);
requires (instanceof[m] == 1) ==> (fracStateMultipleOf3StateLive[this] > 0.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf3StateLimbo[this] > 0.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf3StateSleep[this] > 0.0);

procedure UnpackStateContextMultiple3(m:Ref, this:Ref);
requires packedStateContextMultiple3[this];
requires fracStateContextMultiple3[this] > 0.0;
ensures (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf3StateLive[this] > 0.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf3StateLimbo[this] > 0.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf3StateSleep[this] > 0.0);

procedure PackBasicFieldsContext(m:Ref, this:Ref);
requires packedBasicFieldsContext[this] == false;
requires (myState[this] == m);

procedure UnpackBasicFieldsContext(m:Ref, this:Ref);
requires packedBasicFieldsContext[this];
requires fracBasicFieldsContext[this] > 0.0;
ensures (myState[this] == m);

procedure PackStateLive(m:Ref, this:Ref);
requires packedStateLive[this] == false;
requires fracStateLive[this] > 0.0;
requires (myState[this] == m);
requires instanceof[m]==1;

procedure UnpackStateLive(m:Ref, this:Ref);
requires packedStateLive[this];
ensures (myState[this] == m);
ensures instanceof[m]==1;

procedure PackStateLimbo(m:Ref, this:Ref);
requires packedStateLimbo[this] == false;
requires fracStateLimbo[this] > 0.0;
requires (myState[this] == m);
requires instanceof[m]==2;

procedure UnpackStateLimbo(m:Ref, this:Ref);
requires  packedStateLimbo[this];
ensures (myState[this] == m);
ensures instanceof[m]==2;

procedure PackStateSleep(m:Ref, this:Ref);
requires packedStateSleep[this] == false;
requires fracStateSleep[this] > 0.0;
requires (myState[this] == m);
requires instanceof[m]==3;

procedure UnpackStateSleep(m:Ref, this:Ref);
requires packedStateSleep[this];
ensures (myState[this] == m);
ensures instanceof[m]==3;
	
procedure ConstructStateContext(this:Ref) 
modifies cell, myState, instanceof;
ensures instanceof[myState[this]]== 1;
{ 

  call ConstructStateLive(myState[this]);
  instanceof[myState[this]] := 1;
} 

procedure setState(newState:Ref, this:Ref) 
modifies myState, instanceof, packedStateLive, fracStateLive
       , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep;
//TODO these need to be in predicates
ensures myState[this] == newState;
ensures instanceof[myState[this]] == instanceof[newState];

ensures ((old(instanceof[newState]) == 1) ==> ( packedStateLive[this] && (fracStateLive[this] > 0.0)));
ensures	((old(instanceof[newState] == 2)) ==> ( packedStateLimbo[this] && (fracStateLimbo[this] > 0.0)));
ensures	((old(instanceof[newState] == 3)) ==> ( packedStateSleep[this] && (fracStateSleep[this] > 0.0)));
{ 
	myState[this] := newState; 
	instanceof[myState[this]] := instanceof[newState];
  if (instanceof[newState] == 1 ) {
     packedStateLive[this] := true;
     fracStateLive[this] := 0.001;
  }
  if (instanceof[newState] == 2 ) {
     packedStateLimbo[this] := true;
     fracStateLimbo[this] := 0.001;
  }
  if (instanceof[newState] == 3 ) {
     packedStateSleep[this] := true;
     fracStateSleep[this] := 0.001;
  }
} 

procedure computeResultSC(num: int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive,
        packedStateMultipleOf3StateLive , packedStateLimbo, fracStateLimbo
        , packedStateSleep, fracStateSleep, divider, packedMultipleOf, fracMultipleOf;
requires packedStateContextMultiple3[this];
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
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] > 0.0;

ensures (old(instanceof[myState[this]]) == 1) ==> 
        (packedStateLimbo[this] && (fracStateLimbo[this] > 0.0));
ensures (old(instanceof[myState[this]]) == 2) ==> 
        (packedStateSleep[this] && (fracStateSleep[this] > 0.0));
//ensures (old(packedStateSleep[this])  && (old(fracStateSleep[this]) > 0.0) ) ==> 
ensures (old(instanceof[myState[this]]) == 3) ==> 
        (packedStateLive[this] && (fracStateLive[this] > 0.0));

{
var temp : Ref;
call UnpackStateContextMultiple3(myState[this], this);
if (instanceof[myState[this]] == 1) {
	call temp := computeResultStateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := computeResultStateLimbo(this, num, myState[this]);
} else if (instanceof[myState[this]] == 3)  {
	call temp := computeResultStateSleep(this, num, myState[this]);
}
r := temp;
}

procedure computeResult2SC(num: int, this:Ref) returns (r:Ref)
modifies cell, value, myState, instanceof, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep
         , packedStateContextMultiple2, divider, packedMultipleOf, fracMultipleOf;
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
//TODO should not access myState like this, but through the right predicate
// maybe StateLive(old[this])
// TODO need to add something about fractions related to the below
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
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this] > 0.0;
ensures (old(instanceof[myState[this]]) == 1) ==> 
        (packedStateSleep[this] && (fracStateSleep[this] > 0.0));
ensures (old(instanceof[myState[this]]) == 3) ==> 
        (packedStateLimbo[this] && (fracStateLimbo[this] > 0.0));
ensures (old(instanceof[myState[this]]) == 2) ==> 
        (packedStateLive[this] && (fracStateLive[this] > 0.0));
{
var temp : Ref;
call UnpackStateContextMultiple2(myState[this], this);
packedStateContextMultiple2[this] := false;
if (instanceof[myState[this]] == 1) {
	call temp := computeResult2StateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := computeResult2StateLimbo(this, num, myState[this]);
} else if (instanceof[myState[this]] == 3) {
	call temp := computeResult2StateSleep(this, num, myState[this]);
}
call PackStateContextMultiple2(myState[this], this);
packedStateContextMultiple2[this] := true;
r:=temp;

}

procedure stateContextCheckMultiplicity3(this:Ref) returns (b:bool) 
requires packedStateContextMultiple3[this];
requires fracStateContextMultiple3[this] > 0.0;
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] > 0.0;
{ 
var temp : bool;
if (instanceof[myState[this]] == 1) {
	call temp := checkMod3StateLive(myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := checkMod3StateLimbo(myState[this]);
} else {
	call temp := checkMod3StateSleep(myState[this]);
}
b := temp;
} 

procedure stateContextCheckMultiplicity2(this:Ref) returns (b:bool) 
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this] > 0.0;
{ 
var temp : bool;
if (instanceof[myState[this]] == 1) {
	call temp := checkMod2StateLive(myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := checkMod2StateLimbo(myState[this]);
} else {
	call temp := checkMod2StateSleep(myState[this]);
}
b := temp;
} 

//--------------------------------

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
ensures (scon[this] == s);
ensures (fracStateContextMultiple2[s] > 0.0);

procedure PackStateClientMultiple3(s:Ref, this:Ref);
requires (packedStateClientMultiple3[this] == false);
requires (scon[this] == s);
requires (fracStateContextMultiple3[s] > 0.0);

procedure UnpackStateClientMultiple3(s:Ref, this:Ref);
requires packedStateClientMultiple3[this];
requires fracStateClientMultiple3[this] > 0.0;
ensures (scon[this] == s);
ensures (fracStateContextMultiple3[s] > 0.0);

procedure ConstructStateClient(sco:Ref, this:Ref)
{
  
}

procedure stateClientCheckMultiplicity3(this:Ref) returns (r:bool)
requires packedStateClientMultiple3[this];
requires (fracStateClientMultiple3[this] > 0.0);
ensures packedStateClientMultiple3[this];
ensures (fracStateClientMultiple3[this] > 0.0);
{
call r:= stateContextCheckMultiplicity3(scon[this]);
}
 
procedure stateClientCheckMultiplicity2(this:Ref) returns (r:bool)
requires packedStateClientMultiple2[this];
requires (fracStateClientMultiple2[this] > 0.0);
ensures packedStateClientMultiple2[this];
ensures (fracStateClientMultiple2[this] > 0.0);
{
call r := stateContextCheckMultiplicity2(scon[this]);
}
 
procedure main(this:Ref)
modifies cell, packedMultipleOf, fracMultipleOf, instanceof,
        myState, divider, value, fracStateClientMultiple3,
        packedStateClientMultiple3, packedStateMultipleOf3StateLive,
        fracStateMultipleOf3StateLive, packedStateContextMultiple3,
        fracStateContextMultiple3, packedStateMultipleOf2StateLive,
        fracStateMultipleOf2StateLive, packedStateContextMultiple2,
        fracStateContextMultiple2, packedStateClientMultiple2,
        fracStateClientMultiple2, packedStateLive, fracStateLive
         , packedStateLimbo, fracStateLimbo, packedStateSleep, fracStateSleep;
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

call ConstructIntCell(15, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(15, 15, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=15;

call ConstructStateLive2(i1, st1);
packedStateMultipleOf3StateLive[st1] := false;
call PackStateMultipleOf3StateLive(i1, st1);
packedStateMultipleOf3StateLive[st1] := true;
fracStateMultipleOf3StateLive[st1] := 1.0;

instanceof[st1] := 1;

call ConstructStateContext(scontext1);
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

call tempRef := computeResultSC(1, scontext1);
call tempBool := stateClientCheckMultiplicity3(sclient1); 
call tempRef := computeResultSC(2, scontext1); 
call tempBool := stateClientCheckMultiplicity3(sclient2); 
call tempRef := computeResultSC(3, scontext1); 
call tempBool := stateClientCheckMultiplicity3(sclient1); 

call ConstructIntCell(14, i2);
packedMultipleOf[i2] := false;
call PackMultipleOf(14, 14, i2);
packedMultipleOf[i2] := true;
fracMultipleOf[i2] := 1.0;
divider[i2] := 14;

call ConstructStateLive2(i2, st2);
packedStateMultipleOf2StateLive[st2] := false;
call PackStateMultipleOf2StateLive(i2, st2);
packedStateMultipleOf2StateLive[st2] := true;
fracStateMultipleOf2StateLive[st2] := 1.0;

instanceof[st2] := 1;

call ConstructStateContext(scontext2);
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

call tempRef := computeResult2SC(1, scontext2);
call tempBool := stateClientCheckMultiplicity2(sclient3); 
call tempRef := computeResult2SC(2, scontext2); 
call tempBool := stateClientCheckMultiplicity2(sclient4); 
call tempRef := computeResult2SC(3, scontext2); 
call tempBool := stateClientCheckMultiplicity2(sclient3); 			
}

