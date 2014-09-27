//class SimpleCell
type Ref;
type PredicateTypes;
type FractionType = [Ref]int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var fracPredValP, fracPredNextP: FractionType;
 
const null: Ref;

var val: [Ref]int;
var next: [Ref]Ref;
const unique PredValP: PredicateTypes;
const unique PredNextP: PredicateTypes;

//constructor for SimpleCell
procedure ConstructSimpleCell(this: Ref, i: int, obj: Ref);
ensures (val[this] == i) && (next[this] == obj);

procedure PackPredVal(this: Ref);
requires val[this] < 15;

procedure UnpackPredVal(this: Ref);
requires packed[this, PredValP];
ensures val[this] < 15;

procedure PackPredNext(this: Ref);
requires packed[next[this], PredValP] && (fracPredValP[next[this]] >= 34);

procedure UnpackPredNext(this: Ref);
requires packed[this, PredNextP];
ensures packed[next[this], PredValP] && (fracPredValP[next[this]] >= 34);

procedure ChangeVal(this: Ref, r: int)
modifies val;
//the requires has to state that r is <15
requires packed[this, PredValP] && (fracPredValP >= 100);
ensures packed[this, PredValP] && (fracPredValP >= 100);
{
val[this] := r;
}


procedure main()
modifies val, packed, fracPredValP;
{
var a, b, c : Ref;

call ConstructSimpleCell(c, 2, null);

call ConstructSimpleCell(a, 2, c);

call ConstructSimpleCell(b, 3, c);

call ChangeVal(c, 4);

}


