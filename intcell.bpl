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

