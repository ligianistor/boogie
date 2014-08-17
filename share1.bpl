//class DoubleCount
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

procedure PackOK(this:Ref);
requires (dbl[this]==2*val[this]);

procedure UnpackOK(this:Ref);
requires packed[this, OKP];
ensures (dbl[this]==2*val[this]);

procedure increment(this:Ref)
modifies val, dbl, packed, fracOKP;
requires packed[this,OKP] && (fracOKP[this] > 0);
ensures packed[this,OKP] && (fracOKP[this] > 0);
{
call UnpackOK(this);
packed[this, OKP]:=false;
val[this]:=val[this]+1;
dbl[this]:=dbl[this]+2;
call PackOK(this);
packed[this, OKP]:=true;
}
 
//----------------------------------
//class Share

var dc: [Ref]Ref;
var fracShareCountP: FractionType;

const unique ShareCountP: PredicateTypes;

//need to write the ShareCount constructor so that
//we can use new for it

//constructor for Share
procedure ConstructShare(this:Ref, dc_:Ref);
ensures dc[this] == dc_;

procedure PackShareCount(this:Ref);
requires (packed[dc[this], OKP] && (fracOKP[dc[this]] > 0));

procedure UnpackShareCount(this:Ref);
requires packed[this, ShareCountP];
ensures (packed[dc[this], OKP] && (fracOKP[dc[this]] > 0));

procedure touch(this: Ref)
modifies val, dbl, packed, fracOKP, fracShareCountP;
requires packed[this, ShareCountP] && (fracShareCountP[this] > 0);
ensures packed[this, ShareCountP] && (fracShareCountP[this] > 0);
{
call UnpackShareCount(this);
packed[this, ShareCountP]:=false;

//assert packed[dc[this],OKP];
//assert (frac[dc[this],OKP] > 0);
assert (fracShareCountP[this] > 0);
call increment(dc[this]) ;
assert (fracShareCountP[this] > 0);
call PackShareCount(this);
packed[this, ShareCountP]:=true;
assert packed[this, ShareCountP];
assert (fracShareCountP[this] > 0);
}

procedure main()
//need to add absolutely all global variables 
//that are being modified, by this method,
//or transitively by all methods that are called in 
//this procedure
modifies val, dbl, packed, fracOKP, fracShareCountP;
{
var dc0 : Ref;
var share1, share2 : Ref;
//need to state that dc satisfies the OK predicate
assume packed[dc0, OKP];
call ConstructShare(share1, dc0);

call ConstructShare(share2, dc0);

//this assume is for the dc of share1,
//to say that we put it in the OK predicate

assume fracOKP[dc[share1]] > 0;
call PackShareCount(share1);
packed[share1, ShareCountP] := true;
assert packed[share1, ShareCountP];
assert (fracShareCountP[share1] > 0);

call touch(share1);

assume fracOKP[dc[share2]] > 0;
call PackShareCount(share2);
packed[share2, ShareCountP] := true;

assert packed[share2, ShareCountP];
assert (fracShareCountP[share2] > 0);
call touch(share2);

}

