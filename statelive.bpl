
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

call ConstructIntCell(21, num*21, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(21, num*21, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=21;

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

call ConstructIntCell(4, num*4, i1);
packedMultipleOf[i1] := false;
call PackMultipleOf(4, num*4, i1);
packedMultipleOf[i1] := true;
fracMultipleOf[i1] := 1.0;
divider[i1]:=4;

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

