
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

call ConstructIntCell(15, 15, i1);
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

call ConstructIntCell(14, 14, i2);
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

