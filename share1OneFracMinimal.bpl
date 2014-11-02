type Ref;
type PredicateTypes;
type FractionType = [Ref, PredicateTypes] int;
type PackedType = [Ref, PredicateTypes] bool;
var packed: PackedType;
var frac: FractionType;
const null: Ref;

var val: [Ref]int;
var dbl: [Ref]int;
const unique OKP: PredicateTypes;

procedure ConstructDoubleCountOKP(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1) && 
		(packed[this, OKP]) && 
		(frac[this, OKP] >= 100);

procedure ConstructDoubleCount(val1: int, dbl1: int, this: Ref);
	ensures (val[this] == val1) && 
		(dbl[this] == dbl1);

procedure PackOK(this:Ref);
	requires (packed[this, OKP] == false) && 
		(dbl[this]==val[this]*2);

procedure UnpackOK(this:Ref);
	requires packed[this, OKP] &&
		(frac[this, OKP] >= 1);
	ensures (dbl[this]==val[this]*2);


procedure increment(this: Ref)
	modifies val, dbl, packed, frac;
	requires packed[this, OKP]  && 
		(frac[this, OKP] >= 1);
	ensures  packed[this, OKP] && 
		(frac[this, OKP] >= 1);
{
	call UnpackOK(this);
	packed[this, OKP]:=false;
	val[this]:= val[this]+1;
	dbl[this]:= dbl[this]+2;
	call PackOK(this);
	packed[this, OKP]:=true;
}

var dc: [Ref]Ref;

const unique ShareCountP: PredicateTypes;

procedure ConstructShare0(this:Ref, dc_:Ref);
	ensures (dc[this] == dc_) &&
		(packed[this, ShareCountP]) && 
		(frac[this, ShareCountP] >= 100);

procedure ConstructShare(this:Ref, dc_:Ref);
	ensures (dc[this] == dc_);

procedure PackShareCount(this:Ref);
	requires (packed[dc[this], OKP] && 
		(frac[dc[this], OKP] >= 1));

procedure UnpackShareCount(this:Ref);
	requires packed[this, ShareCountP];
	ensures (packed[dc[this], OKP] && 
		(frac[dc[this], OKP] >= 1));

procedure touch(this: Ref)
	modifies val, dbl, packed;
	requires packed[this, ShareCountP];
	requires (frac[this, ShareCountP] >= 1);
	ensures packed[this, ShareCountP] &&
		(frac[this, ShareCountP] >= 1);

	free ensures (forall x : Ref, y : PredicateTypes :: 
		(
		!((x==this) && (y==ShareCountP))
		==> (packed[x,y]==old(packed[x,y]))
		)
	);


{
	call UnpackShareCount(this);
	packed[this, ShareCountP]:=false;
	call increment(dc[this]) ;
	call PackShareCount(this);
	packed[this, ShareCountP]:=true;
}

procedure main()
	modifies val, dbl, packed, frac;
{
	var dc0 : Ref;
	var share1, share2 : Ref;
	call ConstructDoubleCount0(dc0, 2, 4);
	call ConstructShare0(share1, dc0);
	call ConstructShare0(share2, dc0);
	call PackShareCount(share1);
	packed[share1, ShareCountP] := true;
	frac[dc[share1], OKP] := frac[dc[share1], OKP] - 1;
	call PackShareCount(share2);
	packed[share2, ShareCountP] := true;
	frac[dc[share2], OKP] := frac[dc[share2], OKP] - 1;
	call touch(share1);
	frac[share1, ShareCountP] := frac[share1, ShareCountP] -1;
	call touch(share2);
	frac[share2, ShareCountP] := frac[share2, ShareCountP] -1;
}

