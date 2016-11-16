type Ref;
var packedSumOK: [Ref] bool;
var fracSumOK: [Ref] real;
var packedSumGreater0: [Ref] bool;
var fracSumGreater0: [Ref] real;

const null: Ref;

var n: [Ref]int;
var sum: [Ref]real;

procedure PackSumOK(s1:real, n1:int, this:Ref);
requires (packedSumOK[this] == false);
requires (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure UnpackSumOK(s1:real, n1:int, this:Ref);
requires packedSumOK[this];
ensures (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure PackSumGreater0(s1:real, this:Ref);
requires (packedSumGreater0[this] == false);
requires (sum[this] == s1) && (s1 > 0.0);

procedure UnpackSumGreater0(s1:real, this:Ref);
requires packedSumGreater0[this];
ensures (sum[this] == s1) && (s1 > 0.0);

procedure ConstructRealSum(n1:int, this:Ref)
modifies n, sum;
{
n[this]:=n1;
call calculateRealSum(n[this], this);
}

procedure calculateRealSum(n1: int, this:Ref) 
modifies sum;
{
	sum[this] := n1 * (n1 + 1) / 2;
}

procedure calculateSum()  returns (r:real, this:Ref)

{ 
	r:= sum[this];
}

procedure sumIsOK() returns (r:bool, this:Ref) {
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
}

procedure sumIsGreater0(this:Ref)  returns (r:bool)
{
	r:= (sum[this] > 0.0);
}



