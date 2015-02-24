type Ref;
type FractionType = [Ref] real;
type PackedType = [Ref] bool;
//divide packed for each PredicateType
//In Boogie it is always better for things to be as separate as 
//possible because of the modifies.
var packedOK: PackedType;
var fracOK: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;

procedure ConstructDoubleCount(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1);

procedure PackOK(this:Ref);
	requires (packedOK[this] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOK(this:Ref);
	requires packedOK[this] &&
		(fracOK[this] > 0.0);
	ensures (dbl[this]==val[this]*2);


procedure increment(this: Ref)
	modifies val, dbl, packedOK;
	requires packedOK[this]  && 
		(fracOK[this] > 0.0);
	ensures  packedOK[this] && 
		(fracOK[this] > 0.0);
	ensures (forall x:Ref :: (packedOK[x] == old(packedOK[x])));
{
	call UnpackOK(this);
	packedOK[this] := false;
	val[this] := val[this]+1;
	dbl[this] := dbl[this]+2;
	call PackOK(this);
	packedOK[this] := true;
}
//----------------------------------
//class Share

var packedShareCount: PackedType;
var fracShareCount: FractionType;

var dc: [Ref]Ref;

//Constructor for Share
//that packs to ShareCount.
//When we construct to a certain predicate,
//it is as if we pack to that predicate, so we need to look
//at the requires of the corresponding "Pack" procedure

procedure ConstructShare(dc1:Ref, this:Ref);
	ensures (dc[this] == dc1);

procedure PackShareCount(this:Ref);
	requires (packedShareCount[this] == false) &&
		(fracOK[dc[this]] > 0.0) ;

//The Pack and Unpack for a predicate must have the same lower bound for 
//frac..[same object].
procedure UnpackShareCount(this:Ref);
	requires packedShareCount[this];
	ensures (fracOK[dc[this]] > 0.0);

procedure touch(this: Ref)
	modifies val, dbl, packedShareCount, packedOK, fracOK;
	requires packedShareCount[this];
	requires (fracShareCount[this] > 0.0);
  requires (forall x:Ref :: packedOK[x]);
  requires (forall x:Ref :: packedShareCount[x]);
	ensures packedShareCount[this] &&
		(fracShareCount[this] > 0.0);
  ensures (forall x:Ref :: (packedOK[x] == old(packedOK[x])));
  ensures (forall x:Ref :: (packedShareCount[x] == old(packedShareCount[x])));
{
	call UnpackShareCount(this);
// We only need to call the unpack here because we want to get to the predicate OK,
// not because we are modifying dc[this] or because we are calling a method on it.
	packedShareCount[this]:=false;
	call increment(dc[this]) ;
	fracOK[dc[this]] := fracOK[dc[this]] / 2.0;
	fracOK[dc[this]] := fracOK[dc[this]] * 2.0;
	call PackShareCount(this);
	packedShareCount[this]:=true;
}

procedure main()
	//need to add absolutely all global variables 
	//that are being modified, by this method,
	//or transitively by all methods that are called in 
	//this procedure
	modifies val, dbl, packedShareCount, packedOK, fracOK, fracShareCount;
    requires (forall x:Ref :: packedOK[x]);
  requires (forall x:Ref :: packedShareCount[x]);
{
	//dc0 also needs to be constructed
	var dc0 : Ref;
	var share1 : Ref;
	var share2 : Ref;

	//Need to state that dc0 satisfies the OK predicate.
	//By calling the constructor we state the invariant for dc0.
	call ConstructDoubleCount(2, 4, dc0);
  packedOK[dc0] := true;
  fracOK[dc0] := 1.0;
	
	//By calling this constructor for share1,
	//we say that we put it in the Share predicate.
	call ConstructShare(share1, dc0);
	fracOK[dc[share1]] := fracOK[dc[share1]] / 2.0;
  packedShareCount[share1] := true;
  fracShareCount[share1] := 1.0;
	
	call ConstructShare(share2, dc0);
	fracOK[dc[share2]] := fracOK[dc[share2]] / 2.0;
  packedShareCount[share2] := true;
  fracShareCount[share2] := 1.0;

	call touch(share1);
	fracShareCount[share1] := fracShareCount[share1] / 2.0;
	fracShareCount[share1] := fracShareCount[share1] * 2.0;
	
	call touch(share2);
	fracShareCount[share2] := fracShareCount[share2] / 2.0;
	fracShareCount[share2] := fracShareCount[share2] * 2.0;
}


