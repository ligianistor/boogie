
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
assume (r!=this);

call ConstructIntCell(33, num*33, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(33, num*33, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=33;

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
assume (r!=this);

call ConstructIntCell(14, num*14, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(14, num*14, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=14;

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

