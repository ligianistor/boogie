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
ensures (myState[this] == m);
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
ensures (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf3StateLive[m] > 0.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf3StateLimbo[m] > 0.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf3StateSleep[m] > 0.0);

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

