//class SimpleCell
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

//Constructor for SimpleCell that ensures PredVal.
//Another constructor that ensures another predicate will
//have another number of arguments.
//This constructor packs to PredVal
procedure ConstructSimpleCell0(this: Ref, i: int, obj: Ref);
	ensures (val[this] == i) && 
		(next[this] == obj) && 
		(packed[this, PredValP]) && 
		(frac[this, PredValP] >= 100);

//This constructor packs to PredNext.
//The difference between this constructor and
//the one above is only the number of arguments.
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
	//The requires has to state that r is < 15.
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
	//Pi now has c@100 PredVal().
	//The asserts below are just to make things clearer, they are 
	//not needed in the proof.
	assert (packed[c, PredValP]) && 
		(frac[c, PredValP] >= 100);

	//This constructor consumes a fraction of the predicate PredVal() to c.
	//We can see this by looking at the requires.

	call ConstructSimpleCell1(a, 2, c);
	//Pi now has c@100 PredVal() && a@100 PredNext().
	assert (val[a] == 2) && 
		(next[a] == c);
	assert (packed[a, PredNextP]) && 
		(frac[a, PredNextP] >= 100);
		frac[c, PredValP] := frac[c, PredValP]-1;
	//Because of the assert above we can call UnpackPredNext(a).

	call ConstructSimpleCell1(b, 3, c);
	//Pi now has c@100 PredVal() && a@100 PredNext() && b@100 PredNext().
	assert (val[b] == 3) && 
		(next[b] == c);
	assert (packed[b, PredNextP]) && 
		(frac[b, PredNextP] >= 100);
    	//This is the way we keep track of fractions.
    	//A fraction of 1 was consumed so we subtract it from fracPredValP
   	frac[c, PredValP] := frac[c, PredValP]-1;
   
	//We need to figure out which object propositions to unpack from Pi,
	//in an automatic way.
	//I have a procedure for this.

	call UnpackPredNext(a);
	//We add 1 to fracPredValP because PredNext contains a fraction of 
	//at least 1 to next[a]. 
	frac[next[a], PredValP] := frac[next[a], PredValP]+1;
	packed[a,PredNextP] := false;
	//We do not need the assert below.
	//I put it in for clarity.
	//assert next[a] == c;

	call UnpackPredNext(b);
	//We make the modification to frac after the call to the resp. procedure.
	frac[next[b], PredValP] := frac[next[b], PredValP]+1;
	packed[b,PredNextP] := false;
	//We do not need the assert below.
	//I put it in for clarity.
	//assert next[b] == c;

	call ChangeVal(c, 4);
}
