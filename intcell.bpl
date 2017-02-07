//intcell.bpl
type Ref;
const null: Ref;

var value: [Ref]int;
var divider : [Ref]int;
var packedMultipleOf: [Ref] bool;
var fracMultipleOf: [Ref] real;

var packedBasicIntCell: [Ref] bool;
var fracBasicIntCell: [Ref] real;

var packedIntCellMany : [Ref] bool;
var fracIntCellMany : [Ref]real;

var packedIntCellFew : [Ref] bool;
var fracIntCellFew : [Ref]real;

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

procedure PackBasicIntCell(a: int, v:int, this:Ref);
requires (packedBasicIntCell[this]==false);
requires (value[this] == v);
requires (divider[this] == a);

procedure UnpackBasicIntCell(a: int, v:int, this:Ref);
requires packedBasicIntCell[this];
requires fracBasicIntCell[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);

procedure PackMultipleOf(a: int, v:int, this:Ref);
requires (packedMultipleOf[this]==false);
requires (value[this] == v);
requires (divider[this] == a);
requires ( (v - int(v/a)*a )==0);

procedure UnpackMultipleOf(a: int, v:int, this:Ref);
requires packedMultipleOf[this];
requires fracMultipleOf[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == a);
ensures	 ( (v - int(v/a)*a )==0);

procedure PackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires (packedIntCellMany[this]==false);
requires (value[this] == val);
requires (divider[this] == divi);
requires (quot >= 10);

procedure UnpackIntCellMany(divi: int, val:int, quot:int, this:Ref);
requires packedIntCellMany[this];
requires fracIntCellMany[this] > 0.0;
ensures	(value[this] == val);
ensures (divider[this] == divi);
ensures (quot >= 10);

procedure PackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires (packedIntCellFew[this]==false);
requires (value[this] == v);
requires (divider[this] == divi);
requires (quot <= 4);

procedure UnpackIntCellFew(divi: int, v:int, quot:int, this:Ref);
requires packedIntCellFew[this];
requires fracIntCellFew[this] > 0.0;
ensures	(value[this] == v);
ensures (divider[this] == divi);
ensures (quot <= 4);

procedure ConstructIntCell(divider1: int, value1: int, this: Ref)
modifies divider, value;
ensures (value[this] == value1);
ensures (divider[this] == divider1);
{
	value[this] := value1;
	divider[this] := divider1;
}

procedure getValueInt(this: Ref) returns (r:int)
{
	r := value[this];
}

