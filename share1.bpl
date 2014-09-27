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
modifies val, dbl, packed;
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

//constructor for Share
procedure ConstructShare(this:Ref, dc_:Ref);
ensures dc[this] == dc_;

procedure PackShareCount(this:Ref);
requires (packed[dc[this], OKP] && (fracOKP[dc[this]] > 0));

procedure UnpackShareCount(this:Ref);
requires packed[this, ShareCountP];
ensures (packed[dc[this], OKP] && (fracOKP[dc[this]] > 0));

procedure touch(this: Ref)
modifies val, dbl, packed;
requires packed[this, ShareCountP] && (fracShareCountP[this] > 0);
ensures packed[this, ShareCountP] && (fracShareCountP[this] > 0);
//the way we automatically write this "free ensures" is described in point 4
//in my email
free ensures (forall x : Ref, y : PredicateTypes :: 
(
!((x==this) && (y==ShareCountP))
==> (packed[x,y]==old(packed[x,y]))
)
);
{
call UnpackShareCount(this);
packed[this, ShareCountP]:=false;

assert (fracShareCountP[this] > 0);
call increment(dc[this]) ;
assert (fracShareCountP[this] > 0);
call PackShareCount(this);
packed[this, ShareCountP]:=true;
}

procedure main()
//need to add absolutely all global variables 
//that are being modified, by this method,
//or transitively by all methods that are called in 
//this procedure
modifies val, dbl, packed;
{
var dc0 : Ref;
var share1, share2 : Ref;
//need to state that dc0 satisfies the OK predicate
//this is the way we state the invariant for dc0
assume packed[dc0, OKP];


call ConstructShare(share1, dc0);
//this assume is for the dc of share1,
//to say that we put it in the OK predicate
assume fracOKP[dc[share1]] > 0;

call ConstructShare(share2, dc0);
//this assume is for the dc of share2,
//to say that we put it in the OK predicate
assume fracOKP[dc[share2]] > 0;


//the 3 lines below are for creating the
//object proposition
//share1@k ShareCount
call PackShareCount(share1);
packed[share1, ShareCountP] := true;
assume (fracShareCountP[share1] > 0);

call touch(share1);

//the 3 lines below are for creating the
//object proposition
//share2@k ShareCount
call PackShareCount(share2);
packed[share2, ShareCountP] := true;
assume (fracShareCountP[share2] > 0);

call touch(share2);
}

