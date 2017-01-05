type Ref;
const null: Ref;

var value: [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedMultipleOf21: [Ref] bool;
var fracMultipleOf21: [Ref] real;

var packedMultipleOf16: [Ref] bool;
var fracMultipleOf16: [Ref] real;

var packedMultipleOf15: [Ref] bool;
var fracMultipleOf15: [Ref] real;

var packedMultipleOf14: [Ref] bool;
var fracMultipleOf14: [Ref] real;

var packedMultipleOf33: [Ref] bool;
var fracMultipleOf33: [Ref] real;

var packedMultipleOf4: [Ref] bool;
var fracMultipleOf4: [Ref] real;


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

// TODO maybe need to add a field value that holds a, the one we divide by
procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false) &&
 	(value[this] == v) && (modulo(v,a) == 0); 

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,a) == 0); 

procedure PackMultipleOf21(v:int, this:Ref);
requires (packedMultipleOf21[this]==false) &&
 	(value[this] == v) && (modulo(v,21) == 0); 

procedure UnpackMultipleOf21(v:int, this:Ref);
requires packedMultipleOf21[this];
requires fracMultipleOf21[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,21) == 0); 

procedure PackMultipleOf16(v:int, this:Ref);
requires (packedMultipleOf16[this]==false) &&
 	(value[this] == v) && (modulo(v,16) == 0); 

procedure UnpackMultipleOf16(v:int, this:Ref);
requires packedMultipleOf16[this];
requires fracMultipleOf16[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,16) == 0);

procedure PackMultipleOf15(v:int, this:Ref);
requires (packedMultipleOf15[this]==false) &&
 	(value[this] == v) && (modulo(v,15) == 0); 

procedure UnpackMultipleOf15(v:int, this:Ref);
requires packedMultipleOf15[this];
requires fracMultipleOf15[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,15) == 0);

procedure PackMultipleOf14(v:int, this:Ref);
requires (packedMultipleOf14[this]==false) &&
 	(value[this] == v) && (modulo(v,14) == 0); 

procedure UnpackMultipleOf14(v:int, this:Ref);
requires packedMultipleOf14[this];
requires fracMultipleOf14[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,14) == 0);

procedure PackMultipleOf33(v:int, this:Ref);
requires (packedMultipleOf33[this]==false) &&
 	(value[this] == v) && (modulo(v,33) == 0); 

procedure UnpackMultipleOf33(v:int, this:Ref);
requires packedMultipleOf33[this];
requires fracMultipleOf33[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,33) == 0);

procedure PackMultipleOf4(v:int, this:Ref);
requires (packedMultipleOf4[this]==false) &&
 	(value[this] == v) && (modulo(v,4) == 0); 

procedure UnpackMultipleOf4(v:int, this:Ref);
requires packedMultipleOf4[this];
requires fracMultipleOf4[this] > 0.0;
ensures	(value[this] == v) && (modulo(v,4) == 0);

procedure ConstructIntCell(x: int, this: Ref);
	ensures (value[this] == x);

procedure setValue(x: int, this: Ref) 
modifies value;
{
	value[this] := x;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r:=value[this];
}

//----------------------

var cell : [Ref]Ref;
var instanceof : [Ref]int;

var packedBasicFieldsStateLive: [Ref] bool;
var fracBasicFieldsStateLive: [Ref] real;

var packedStateMultipleOf3StateLive: [Ref]bool;
var fracStateMultipleOf3StateLive: [Ref]real;

var packedStateMultipleOf2StateLive: [Ref]bool;
var fracStateMultipleOf2StateLive: [Ref]real;

procedure PackBasicFieldsStateLive(c: Ref, this: Ref);
requires (packedBasicFieldsStateLive[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateLive(c: Ref, this: Ref);
requires packedBasicFieldsStateLive[this];
requires fracBasicFieldsStateLive[this] > 0.0;
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateLive(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf15[c] == 1.0);

procedure UnpackStateMultipleOf3StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLive[this];
requires fracStateMultipleOf3StateLive[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf15[c] == 1.0);

procedure PackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf14[c] == 1.0);

procedure UnpackStateMultipleOf2StateLive(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLive[this];
requires fracStateMultipleOf2StateLive[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf14[c] == 1.0);

procedure ConstructStateLive(this:Ref)
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateLive2(temp, cell[this]);
}

procedure ConstructStateLive2(c:Ref, this:Ref)
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLive[this] && (fracBasicFieldsStateLive[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateLive[this] && (fracStateMultipleOf3StateLive[this] >= 1.0);
ensures packedStateLimbo[context] && (fracStateLimbo[context] >= 1.0);
{
var s : Ref;
call ConstructStateLimbo(s);
// StateLike s = new StateLimbo()[];
call setValue(num*15, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateLive(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLive[this] && (fracBasicFieldsStateLive[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures packedStateSleep[context] && (fracStateSleep[context] >= 1.0);
{
var s : Ref;
call ConstructStateSleep(s);
// StateLike s = new StateSleep()[];
call setValue(num*14, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure checkMod3StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateLive[this] && (fracStateMultipleOf3StateLive[this] >= 1.0);
ensures packedStateMultipleOf3StateLive[this] && (fracStateMultipleOf3StateLive[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b:= (modulo(temp, 3) == 0);
}

procedure checkMod2StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b:= (modulo(temp, 2) == 0);
}

//--------------------------------------------

var packedBasicFieldsStateLimbo: [Ref] bool;
var fracBasicFieldsStateLimbo: [Ref] real;

var packedStateMultipleOf3StateLimbo: [Ref]bool;
var fracStateMultipleOf3StateLimbo: [Ref]real;

var packedStateMultipleOf2StateLimbo: [Ref]bool;
var fracStateMultipleOf2StateLimbo: [Ref]real;

procedure PackBasicFieldsStateLimbo(c: Ref, this: Ref);
requires (packedBasicFieldsStateLimbo[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateLimbo(c: Ref, this: Ref);
requires packedBasicFieldsStateLimbo[this];
requires fracBasicFieldsStateLimbo[this] > 0.0;
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf21[c] == 1.0);

procedure UnpackStateMultipleOf3StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf3StateLimbo[this];
requires fracStateMultipleOf3StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf21[c] == 1.0);

procedure PackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf16[c] == 1.0);

procedure UnpackStateMultipleOf2StateLimbo(c:Ref, this:Ref);
requires packedStateMultipleOf2StateLimbo[this];
requires fracStateMultipleOf2StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf16[c] == 1.0);

procedure ConstructStateLimbo(this:Ref)
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateLimbo2(temp, cell[this]);
}

procedure ConstructStateLimbo2(c:Ref, this:Ref)
ensures cell[this] == c;
{	
	cell[this] := c;
}


procedure computeResultStateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLimbo[this] && (fracBasicFieldsStateLimbo[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateLimbo[this] && (fracStateMultipleOf3StateLimbo[this] >= 1.0);
ensures packedStateSleep[context] && (fracStateSleep[context] >= 1.0);
{
var s : Ref;
call ConstructStateSleep(s);
// StateLike s = new StateSleep()[];
call setValue(num*21, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateLimbo(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLimbo[this] && (fracBasicFieldsStateLimbo[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures packedStateLive[context] && (fracStateLive[context] >= 1.0);
{
var s : Ref;
call ConstructStateLive(s);
// StateLike s = new StateLive()[];
call setValue(num*16, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure checkMod3StateLimbo(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateLimbo[this] && (fracStateMultipleOf3StateLimbo[this] >= 1.0);
ensures packedStateMultipleOf3StateLimbo[this] && (fracStateMultipleOf3StateLimbo[this] >= 1.0);
{
var temp : int;
call temp := getValueInt(cell[this]);
b := (modulo(temp, 3) == 0);
}

procedure checkMod2StateLimbo(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b := (modulo(temp, 2) == 0);
}

//-----------------------------------------

var packedBasicFieldsStateSleep: [Ref] bool;
var fracBasicFieldsStateSleep: [Ref] real;

var packedStateMultipleOf3StateSleep: [Ref]bool;
var fracStateMultipleOf3StateSleep: [Ref]real;

var packedStateMultipleOf2StateSleep: [Ref]bool;
var fracStateMultipleOf2StateSleep: [Ref]real;

procedure PackBasicFieldsStateSleep(c: Ref, this: Ref);
requires (packedBasicFieldsStateSleep[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateSleep(c: Ref, this: Ref);
requires packedBasicFieldsStateSleep[this];
requires fracBasicFieldsStateSleep[this] > 0.0;
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf3StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf33[c] == 1.0);

procedure UnpackStateMultipleOf3StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf3StateSleep[this];
requires fracStateMultipleOf3StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf33[c] == 1.0);

procedure PackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires (packedStateMultipleOf2StateSleep[this] == false);
requires (cell[this] == c);
// should this be fracMultipleOf2??
requires (fracMultipleOf4[c] == 1.0);

procedure UnpackStateMultipleOf2StateSleep(c:Ref, this:Ref);
requires packedStateMultipleOf2StateSleep[this];
requires fracStateMultipleOf2StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf4[c] == 1.0);

procedure ConstructStateSleep(this:Ref)
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateSleep2(temp, cell[this]);
}

procedure ConstructStateSleep2(c:Ref, this:Ref)
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateSleep(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateSleep[this] && (fracBasicFieldsStateSleep[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateSleep[this] && (fracStateMultipleOf3StateSleep[this] >= 1.0);
ensures packedStateLive[context] && (fracStateLive[context] >= 1.0);
{
var s : Ref;
call ConstructStateLive(s);
// StateLike s = new StateLive()[];
call setValue(num*33, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateSleep(context:Ref, num:int, this:Ref) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateSleep[this] && (fracBasicFieldsStateSleep[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
ensures packedStateLimbo[context] && (fracStateLimbo[context] >= 1.0);
{
var s : Ref;
call ConstructStateLimbo(s);
// StateLike s = new StateLimbo()[];
call setValue(num*14, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure checkMod3StateSleep(this:Ref) returns (b:bool)
requires packedStateMultipleOf3StateSleep[this] && (fracStateMultipleOf3StateSleep[this] >= 1.0);
ensures packedStateMultipleOf3StateSleep[this] && (fracStateMultipleOf3StateSleep[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
b := (modulo(temp, 3) == 0);
}

procedure checkMod2StateSleep(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
ensures packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
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
requires (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] >= 1.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] >= 1.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] >= 1.0);

procedure UnpackStateContextMultiple2(m:Ref, this:Ref);
requires packedStateContextMultiple2[this];
requires fracStateContextMultiple2[this] > 0.0;
ensures (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] >= 1.0);

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



//	predicate BasicFieldsContext() = exists m:StateLike :: this.myState -> m

//	predicate stateLive() =  exists m:StateLike :: this.myState -> m && instanceof[m]==1;
//	predicate stateLimbo() = exists m:StateLike :: this.myState -> m && instanceof[m]==2;
//	predicate stateSleep() = exists m:StateLike :: this.myState -> m && instanceof[m]==3;

//	predicate stateContextMultiple2() = myState#1 StateMultipleOf2() 
//	predicate stateContextMultiple3() = myState#1 StateMultipleOf3() 
	
procedure ConstructStateContext(this:Ref) 
ensures instanceof[this] == 1;
{ 
  var temp:Ref;
  call ConstructStateLive(temp);
	call setState(temp, this); 
} 

procedure setState(newState:Ref, this:Ref) 
modifies myState;
{ 
	myState[this] := newState; 
} 

procedure computeResultSC(num: int, this:Ref) returns (r:Ref)
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] >= 1.0;
ensures (old(instanceof[myState[this]]) == 1) ==> (instanceof[myState[this]] == 2);
ensures (old(instanceof[myState[this]]) == 2) ==> (instanceof[myState[this]] == 3);
ensures (old(instanceof[myState[this]]) == 3) ==> (instanceof[myState[this]] == 1);
{
var temp : Ref;
if (instanceof[myState[this]] == 1) {
	call temp := computeResultStateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := computeResultStateLimbo(this, num, myState[this]);
} else {
	call temp := computeResultStateSleep(this, num, myState[this]);
}
}

procedure computeResult2SC(num: int, this:Ref) returns (r:Ref)
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this] >= 1.0;
//TODO should not access myState like this, but through the right predicate
// maybe StateLive(old[this])
// TODO need to add something about fractions related to the below
ensures (old(instanceof[myState[this]]) == 1) ==> (instanceof[myState[this]] == 3);
ensures (old(instanceof[myState[this]]) == 3) ==> (instanceof[myState[this]] == 2);
ensures (old(instanceof[myState[this]]) == 2) ==> (instanceof[myState[this]] == 1);
{
var temp : Ref;
if (instanceof[myState[this]] == 1) {
	call temp := computeResult2StateLive(this, num, myState[this]);
} else if (instanceof[myState[this]] == 2) {
	call temp := computeResult2StateLimbo(this, num, myState[this]);
} else {
	call temp := computeResult2StateSleep(this, num, myState[this]);
}
r:=temp;
}

procedure stateContextCheckMultiplicity3(this:Ref) returns (b:bool) 
requires packedStateContextMultiple3[this];
requires fracStateContextMultiple3[this] == 1.0;
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] == 1.0;
{ 
var temp : Ref;
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
requires fracStateContextMultiple2[this] == 1.0;
ensures packedStateContextMultiple2[this];
ensures fracStateContextMultiple2[this]== 1.0;
{ 
var temp : Ref;
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
requires (packedStateClientMultiple2[this] ==false);
requires (scon[this] == s);
requires (fracStateContextMultiple2[s] > 0.0);

procedure UnpackStateClientMultiple2(s:Ref, this:Ref);
requires packedStateClientMultiple2[this];
requires fracStateClientMultiple2[this] > 0.0;
ensures (scon[this] == s);
ensures (fracStateContextMultiple2[s] > 0.0);

procedure PackStateClientMultiple3(s:Ref, this:Ref);
requires (packedStateClientMultiple3[this] ==false);
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
requires (fracStateClientMultiple3[this] >= 1.0);
ensures packedStateClientMultiple3[this];
ensures (fracStateClientMultiple3[this] >= 1.0);
{
call r:= stateContextCheckMultiplicity3(scon[this]);
}
 
procedure stateClientCheckMultiplicity2(this:Ref) returns (r:bool)
requires packedStateClientMultiple2[this];
requires (fracStateClientMultiple2[this] >= 1.0);
ensures packedStateClientMultiple2[this];
ensures (fracStateClientMultiple2[this] >= 1.0);
{
call r := stateContextCheckMultiplicity2(scon[this]);
}
 
procedure main(this:Ref)
{
var i1, i2 : Ref;
var st1, st2 : Ref;
var scontext1, scontext2 : Ref;
var sclient1, sclient2, sclient3, sclient4 : Ref;

assume (i1 != i2);
assume (st1 != st2);
assume (sclient1 != sclient2);
assume (sclient3 != sclient4);
assume (scontext1 != scontext2);

call ConstructIntCell(15, i1);
packedMultipleOf15[i1] := false;
call PackMultipleOf15(15, i1);
packedMultipleOf15[i1] := true;
fracMultipleOf15[i1] := 1.0;

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

call computeResult(1, scontext1);
call stateClientCheckMultiplicity3(sclient1); 
call computeResult(2, scontext1); 
call stateClientCheckMultiplicity3(sclient2); 
call computeResult(3, scontext1); 
call stateClientCheckMultiplicity3(sclient1); 

call ConstructIntCell(14, i2);
packedMultipleOf14[i2] := false;
call PackMultipleOf14(14, i2);
packedMultipleOf14[i2] := true;
fracMultipleOf14[i2] := 1.0;

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

call computeResult2SC(1, scontext2);
call stateClientCheckMultiplicity2(sclient3); 
call computeResult2SC(2, scontext2); 
call stateClientCheckMultiplicity2(sclient4); 
call computeResult2SC(3, scontext2); 
call stateClientCheckMultiplicity2(sclient3); 			
}

