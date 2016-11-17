type Ref;
const null: Ref;

var value: [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedMultipleOf3: [Ref] bool;
var fracMultipleOf3: [Ref] real;

var packedMultipleOf2: [Ref] bool;
var fracMultipleOf2: [Ref] real;

var packedMultipleOf6: [Ref] bool;
var fracMultipleOf6: [Ref] real;

var packedMultipleOf18: [Ref] bool;
var fracMultipleOf18: [Ref] real;


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

procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false) &&
 	(value[this] == v) && (modulo(v,a) == 0); 

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
ensures	(value[this] == v) && (modulo(v,a) == 0); 

procedure PackMultipleOf3(v:int, this:Ref);
requires (packedMultipleOf3[this]==false) &&
 	(value[this] == v) && (modulo(v,3) == 0); 

procedure UnpackMultipleOf3(v:int, this:Ref);
requires packedMultipleOf3[this];
ensures	(value[this] == v) && (modulo(v,3) == 0); 

//predicate MultipleOf2() = value->v && (v % 2 == 0) 
//predicate MultipleOf6() = value->v && (v % 6 == 0) 
//predicate MultipleOf18() = value->v && (v % 18 == 0) 
//maybe these can be expressed through MultipleOf

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

