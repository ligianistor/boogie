type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes]int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var frac: FractionType;
 
const null: Ref;

var val: [Ref]int;
var next: [Ref]Ref;
const unique PredValP: PredicateTypes;
const unique PredNextP: PredicateTypes;

procedure ConstructSimpleCell0(this: Ref, i: int, obj: Ref);
	ensures (val[this] == i) && 
		(next[this] == obj) && 
		(packed[this, PredValP]) && 
		(frac[this, PredValP] >= 100);

procedure ConstructSimpleCell1(this: Ref, i: int, obj: Ref);
	requires frac[obj, PredValP] >= 1;
	ensures (val[this] == i) && 
		(next[this] == obj) && 
		(packed[this, PredNextP]) && 
		(frac[this, PredNextP] >= 100);			

procedure PackPredVal(this: Ref);
	requires (packed[this, PredValP] == false) && 
		(val[this] < 15);

procedure UnpackPredVal(this: Ref);
	requires packed[this, PredValP] &&
		(frac[this, PredValP] >= 1);
	ensures val[this] < 15;

procedure PackPredNext(this: Ref);
	requires (packed[this, PredNextP] == false) &&
		packed[next[this], PredValP] && 
		(frac[next[this], PredValP] >= 1);

procedure UnpackPredNext(this: Ref);
	requires packed[this, PredNextP] &&
		(frac[this, PredNextP] >= 1);
	ensures packed[next[this], PredValP] && 
		(frac[next[this], PredValP] >= 1);

procedure ChangeVal(this: Ref, r: int)
	modifies val;
	requires packed[this, PredValP] && 
		(frac[this, PredValP] >= 100);
	ensures packed[this, PredValP] &&
		 (frac[this, PredValP] >= 100);
{
	val[this] := r;
}

procedure main()
	modifies val, packed, frac;
{
	var a, b, c : Ref;

	call ConstructSimpleCell0(c, 2, null);

	call ConstructSimpleCell1(a, 2, c);

	call ConstructSimpleCell1(b, 3, c);

   	frac[c, PredValP] := frac[c, PredValP]-1;

	call UnpackPredNext(a);
	frac[next[a], PredValP] := frac[next[a], PredValP]+1;
	packed[a,PredNextP] := false;

	call UnpackPredNext(b);

	frac[next[b], PredValP] := frac[next[b], PredValP]+1;
	packed[b,PredNextP] := false;

	call ChangeVal(c, 4);
}
