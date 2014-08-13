//class DoubleCount
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

procedure PackOK(this:Ref);
requires (dbl[this]==2*val[this]);

procedure UnpackOK(this:Ref);
requires packed[this, OKP];
ensures (dbl[this]==2*val[this]);

procedure increment(this:Ref)
modifies val, dbl, packed, frac;
requires packed[this,OKP] && (frac[this,OKP] > 0);
ensures packed[this,OKP] && (frac[this,OKP] > 0);
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

const unique ShareCountP: PredicateTypes;

//need to write the ShareCount constructor so that
//we can use new for it

//procedure ShareConstructor();
//ensures ;

procedure PackShareCount(this:Ref);
requires (packed[dc[this], OKP] && (frac[dc[this], OKP] >= 50));

procedure UnpackShareCount(this:Ref);
requires packed[this, ShareCountP];
ensures (packed[dc[this], OKP] && (frac[dc[this], OKP] >= 50));

procedure touch(this: Ref)
modifies val, dbl, packed, frac;
requires packed[this, ShareCountP] && (frac[this, ShareCountP] > 0);
ensures packed[this, ShareCountP] && (frac[this, ShareCountP] > 0);
{
call increment(dc[this]) ;
}

//procedure main()
//{

//}

