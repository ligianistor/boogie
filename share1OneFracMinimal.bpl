type Ref;
type FractionType = [Ref] real;
type PackedType = [Ref] bool;
var packedOK: PackedType;
var fracOK: FractionType;
const null: Ref;

var packedShareCount: PackedType;
var fracShareCount: FractionType;

var dc: [Ref]Ref;

procedure ConstructShareCount(this:Ref, dc_:Ref);
	ensures (dc[this] == dc_) &&
		(packedShareCount[this]) && 
		(fracShareCount[this] == 1.0);

procedure PackShareCount(this:Ref);
	requires (packedOK[dc[this]] && 
		(fracOK[dc[this]] > 0.0));

procedure UnpackShareCount(this:Ref);
	requires packedShareCount[this];
	ensures (packedOK[dc[this]] && 
		(fracOK[dc[this]] > 0.0));

procedure touch(this: Ref)
	modifies val, dbl, packedShareCount, packedOK;
	requires packedShareCount[this];
	requires (fracShareCount[this] > 0.0);
	ensures packedShareCount[this] &&
		(fracShareCount[this] > 0.0);
  ensures (forall x:Ref :: (packedOK[x] == old(packedOK[x])));
  ensures (forall x:Ref :: (packedShareCount[x] == old(packedShareCount[x])));
{
	call UnpackShareCount(this);
	packedShareCount[this]:=false;
	call increment(dc[this]) ;
	call PackShareCount(this);
	packedShareCount[this]:=true;
}

procedure main()
	modifies val, dbl, packedShareCount, packedOK, fracOK, fracShareCount;
{
	var dc0 : Ref;
	var share1, share2 : Ref;

	call ConstructDoubleCountOK(2, 4, dc0);

	call ConstructShareShareCount(share1, dc0);
	fracOK[dc[share1]] := fracOK[dc[share1]] / 2.0;

	call ConstructShareShareCount(share2, dc0);
	fracOK[dc[share2]] := fracOK[dc[share2]] / 2.0;

	call touch(share1);
	fracShareCount[share1] := fracShareCount[share1] / 2.0;

	call touch(share2);
	fracShareCount[share2] := fracShareCount[share2] / 2.0;
}

