var packedBasicFieldsStateLimbo: [Ref] bool;
var fracBasicFieldsStateLimbo: [Ref] real;

var packedStateMultipleOf3StateLimbo: [Ref]bool;
var fracStateMultipleOf3StateLimbo: [Ref]real;

var packedStateMultipleOf2StateLimbo: [Ref]bool;
var fracStateMultipleOf2StateLimbo: [Ref]real;

procedure PackBasicFieldsStateLimbo(c: Ref, this: Ref)
requires (packedBasicFieldsStateLimbo[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateLimbo(c: Ref, this: Ref)
requires packedBasicFieldsStateLimbo[this];
requires fracBasicFieldsStateLimbo[this] > 0.0;
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateLimbo(c:Ref, this:Ref)
requires (packedStateMultipleOf3StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf21[c] == 1.0);

procedure UnpackStateMultipleOf3StateLimbo(c:Ref, this:Ref)
requires packedStateMultipleOf3StateLimbo[this];
requires fracStateMultipleOf3StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf21[c] == 1.0);

procedure PackStateMultipleOf2StateLimbo(c:Ref, this:Ref)
requires (packedStateMultipleOf2StateLimbo[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf16[c] == 1.0);

procedure UnpackStateMultipleOf2StateLimbo(c:Ref, this:Ref)
requires packedStateMultipleOf2StateLimbo[this];
requires fracStateMultipleOf2StateLimbo[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf16[c] == 1.0);

procedure ConstructStateLimbo(this:Ref);
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateLimbo(temp, cell[this]);
}

procedure ConstructStateLimbo(c:Ref, this:Ref);
ensures cell[this] == c;
{	
	cell[this] := c;
}


procedure computeResultStateLimbo(context:Ref, num:int) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLimbo[this] && (fracBasicFieldsStateLimbo[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateLimbo[this] && (fracStateMultipleOf3StateLimbo[this] >= 1.0);
ensures packedStateSleep[context] && (fracStateSleep[context] >= 1.0)
{
var s : Ref;
call ConstructStateSleep(s);
// StateLike s = new StateSleep()[];
call setValue(num*21, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateLimbo(context:Ref, num:int) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLimbo[this] && (fracBasicFieldsStateLimbo[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures packedStateLive[context] && (fracStateLive[context] >= 1.0)
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
r:= (modulo(temp, 3) == 0);
}

procedure checkMod2StateLimbo(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures packedStateMultipleOf2StateLimbo[this] && (fracStateMultipleOf2StateLimbo[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
r:= (modulo(temp, 2) == 0);
}

