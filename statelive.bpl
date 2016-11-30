type Ref;

const null: Ref;

var cell: [Ref]Ref;

var packedBasicFieldsStateLive: [Ref] bool;
var fracBasicFieldsStateLive: [Ref] real;

var packedStateMultipleOf3StateLive: [Ref]bool;
var fracStateMultipleOf3StateLive: [Ref]real;

var packedStateMultipleOf2StateLive: [Ref]bool;
var fracStateMultipleOf2StateLive: [Ref]real;

procedure PackBasicFieldsStateLive(c: Ref, this: Ref)
requires (packedBasicFieldsStateLive[this] == false);
requires (cell[this] == c);

procedure UnpackBasicFieldsStateLive(c: Ref, this: Ref)
requires packedBasicFieldsStateLive[this];
ensures (cell[this] == c);

procedure PackStateMultipleOf3StateLive(c:Ref, this:Ref)
requires (packedStateMultipleOf3StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf15[c] == 1.0);

procedure UnpackStateMultipleOf3StateLive(c:Ref, this:Ref)
requires packedStateMultipleOf3StateLive[this];
ensures (cell[this] == c);
ensures (fracMultipleOf15[c] == 1.0);

procedure PackStateMultipleOf2StateLive(c:Ref, this:Ref)
requires (packedStateMultipleOf2StateLive[this] ==false);
requires (cell[this] == c);
requires (fracMultipleOf14[c] == 1.0);

procedure UnpackStateMultipleOf2StateLive(c:Ref, this:Ref)
requires packedStateMultipleOf32tateLive[this];
ensures (cell[this] == c);
ensures (fracMultipleOf14[c] == 1.0);

procedure ConstructStateLive(c:Ref, this:Ref);
ensures cell[this] == c;


procedure computeResultStateLive(context:Ref, num:int) returns (r:Ref)
modifies
requires packedBasicFieldsStateLive[this] && (fracBasicFieldsStateLive[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf3StateLive[this] && (fracStateMultipleOf3StateLive[this] >= 1.0);
ensures packedStateLimbo[context] && (fracStateLimbo[context] >= 1.0)
{
var s : Ref;
// call constructor of s 
// StateLike s = new StateLive()[];
call setValue(num*33, cell[this]);
call setState(s, context);
r:=cell[this];
}


procedure computeResult2StateLive(context:Ref, num:int) returns (r:Ref)
modifies cell;
requires packedBasicFieldsStateLive[this] && (fracBasicFieldsStateLive[this] >= 1.0);
requires packedBasicFieldsContext[context] && (fracBasicFieldsContext[context] >= 1.0);
ensures packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures packedStateSleep[context] && (fracStateSleep[context] >= 1.0)
{
var s : Ref;
// call constructor of s 
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
r:= (modulo(temp, 3) == 0);
}

procedure checkMod2StateLive(this:Ref) returns (b:bool)
requires packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures packedStateMultipleOf2StateLive[this] && (fracStateMultipleOf2StateLive[this] >= 1.0);
{
var temp : int;
call temp :=getValueInt(cell[this]);
r:= (modulo(temp, 2) == 0);
}

