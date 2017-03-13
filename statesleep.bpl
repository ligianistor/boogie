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

