var packedBasicFieldsStateSleep: [Ref] bool;
var fracBasicFieldsStateSleep: [Ref] real;

var packedStateMultipleOf3StateSleep: [Ref]bool;
var fracStateMultipleOf3StateSleep: [Ref]real;

var packedStateMultipleOf2StateSleep: [Ref]bool;
var fracStateMultipleOf2StateSleep: [Ref]real;

procedure PackBasicFieldsStateSleep(c: Ref, this: Ref)
requires (packedBasicFieldsStateSleep[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateSleep(c: Ref, this: Ref)
requires packedBasicFieldsStateSleep[this];
requires fracBasicFieldsStateSleep[this] > 0.0;
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateSleep(c:Ref, this:Ref)
requires (packedStateMultipleOf3StateSleep[this] == false);
requires (cell[this] == c);
requires (fracMultipleOf33[c] == 1.0);

procedure UnpackStateMultipleOf3StateSleep(c:Ref, this:Ref)
requires packedStateMultipleOf3StateSleep[this];
requires fracStateMultipleOf3StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf33[c] == 1.0);

procedure PackStateMultipleOf2StateSleep(c:Ref, this:Ref)
requires (packedStateMultipleOf2StateSleep[this] == false);
requires (cell[this] == c);
// should this be fracMultipleOf2??
requires (fracMultipleOf4[c] == 1.0);

procedure UnpackStateMultipleOf2StateSleep(c:Ref, this:Ref)
requires packedStateMultipleOf2StateSleep[this];
requires fracStateMultipleOf2StateSleep[this] > 0.0;
ensures (cell[this] == c);
ensures (fracMultipleOf4[c] == 1.0);

procedure ConstructStateSleep(this:Ref);
{	
	var temp:Ref;
	call ConstructIntCell(0, temp);
	call ConstructStateSleep(temp, cell[this]);
}

procedure ConstructStateSleep(c:Ref, this:Ref);
ensures cell[this] == c;
{	
	cell[this] := c;
}

procedure computeResultStateSleep(context:Ref, num:int) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateSleep[this] && (fracBasicFieldsStateSleep[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateSleep[this] && (fracStateMultipleOf3StateSleep[this] >= 1.0);
ensures packedStateLive[context] && (fracStateLive[context] >= 1.0)
{
var s : Ref;
call ConstructStateLive(s);
// StateLike s = new StateLive()[];
call setValue(num*33, cell[this]);
call setState(s, context);
r:=cell[this];
}

procedure computeResult2StateSleep(context:Ref, num:int) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateSleep[this] && (fracBasicFieldsStateSleep[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
ensures packedStateLimbo[context] && (fracStateLimbo[context] >= 1.0)
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
r:= (modulo(temp, 3) == 0);
}

procedure checkMod2StateSleep(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
ensures packedStateMultipleOf2StateSleep[this] && (fracStateMultipleOf2StateSleep[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
r:= (modulo(temp, 2) == 0);
}

