//type Ref represents object references
type Ref;
type PredicateTypes;
type FractionType = [Ref] int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var fracOKP: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;

const unique OKP: PredicateTypes;

//Constructor for DoubleCount that ensures OK.
//Might need to add a ConstructDoubleCount for the default constructor.
procedure ConstructDoubleCount0(this: Ref, v: int, d: int);
	ensures (val[this] == v) && 
		(dbl[this] == d) && 
		(packed[this, OKP]) && 
		(fracOKP[this] >= 100);

procedure PackOk(this:Ref);
	requires (packed[this, OKP] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOk(this:Ref);
	requires packed[this, OKP] &&
		(fracOKP[this] >= 1);
	ensures (dbl[this]==val[this]*2);


procedure increment(this: Ref)
	modifies val, dbl, packed, fracOKP;
	requires packed[this, OKP]  && 
		(fracOKP[this] >= 1);
	ensures  packed[this, OKP] && 
		(fracOKP[this] >= 1);
{
	call UnpackOk(this);
	packed[this, OKP]:=false;
	val[this]:= val[this]+1;
	dbl[this]:= dbl[this]+2;
	call PackOk(this);
	packed[this, OKP]:=true;
}

//----------------------------------
//class Share

var dc: [Ref]Ref;
var fracShareCountP: FractionType;

const unique ShareCountP: PredicateTypes;

//Constructor for Share
//that packs to ShareCount
procedure ConstructShare0(this:Ref, dc_:Ref);
	ensures (dc[this] == dc_) &&
		(packed[this, ShareCountP]) && 
		(fracShareCountP[this] >= 100);

//Use >= instead of > when writing about frac.
//It will be easier for the Oprop plugin to find the lower bound.
procedure PackShareCount(this:Ref);
	requires (packed[dc[this], OKP] && 
		(fracOKP[dc[this]] >= 1));

//The Pack and Unpack for a predicate must have the same lower bound for 
//frac..[same object].
procedure UnpackShareCount(this:Ref);
	requires packed[this, ShareCountP];
	ensures (packed[dc[this], OKP] && 
		(fracOKP[dc[this]] >= 1));

procedure touch(this: Ref)
	modifies val, dbl, packed, fracOKP;
	requires packed[this, ShareCountP] && 
		(fracShareCountP[this] >= 1);
	ensures packed[this, ShareCountP] &&
		(fracShareCountP[this] >= 1);
	//The way we automatically write this "free ensures" is described in point 4
	//in my email.
	free ensures (forall x : Ref, y : PredicateTypes :: 
		(
		!((x==this) && (y==ShareCountP))
		==> (packed[x,y]==old(packed[x,y]))
		)
	);
{
	call UnpackShareCount(this);
	packed[this, ShareCountP]:=false;

	assert (fracShareCountP[this] >= 1);
	call increment(dc[this]) ;
	assert (fracShareCountP[this] >= 1);
	call PackShareCount(this);
	packed[this, ShareCountP]:=true;
}

procedure main()
	//need to add absolutely all global variables 
	//that are being modified, by this method,
	//or transitively by all methods that are called in 
	//this procedure
	modifies val, dbl, packed, fracOKP, fracShareCountP;
{
	//dc0 also needs to be constructed
	var dc0 : Ref;
	var share1, share2 : Ref;
	//Need to state that dc0 satisfies the OK predicate.
	//By calling the constructorwe state the invariant for dc0.
	call ConstructDoubleCount0(dc0, 2, 4);


	//By calling this constructorfor share1,
	//we say that we put it in the Share predicate.
	call ConstructShare0(share1, dc0);


	call ConstructShare0(share2, dc0);


	//The 2 lines below are for creating the
	//object proposition
	//share1@k ShareCount.
	call PackShareCount(share1);
	packed[share1, ShareCountP] := true;
	fracOKP[dc[share1]] := fracOKP[dc[share1]] - 1;

	//The 2 lines below are for creating the
	//object proposition
	//share2@k ShareCount.
	call PackShareCount(share2);
	packed[share2, ShareCountP] := true;
	fracOKP[dc[share2]] := fracOKP[dc[share2]] - 1;

	call touch(share1);
	fracShareCountP[share1] := fracShareCountP[share1] -1;

	call touch(share2);
	fracShareCountP[share2] := fracShareCountP[share2] -1;
}

