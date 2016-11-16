type Ref;
var packedSumOKRealSum: [Ref] bool;
var fracSumOKRealSum: [Ref] real;
var packedSumGreater0RealSum: [Ref] bool;
var fracSumGreater0RealSum: [Ref] real;

const null: Ref;

var n: [Ref]int;
var sum: [Ref]real;

procedure PackSumOKRealSum(s1:real, n1:int, this:Ref);
requires (packedSumOKRealSum[this] == false);
requires (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure UnpackSumOKRealSum(s1:real, n1:int, this:Ref);
requires packedSumOKRealSum[this];
ensures (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure PackSumGreater0RealSum(s1:real, this:Ref);
requires (packedSumGreater0RealSum[this] == false);
requires (sum[this] == s1) && (s1 > 0.0);

procedure UnpackSumGreater0RealSum(s1:real, this:Ref);
requires packedSumGreater0RealSum[this];
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

procedure calculateSumRealSum(this:Ref)  returns (r:real)

{ 
	r:= sum[this];
}

procedure sumIsOKRealSum( this:Ref) returns (r:bool) {
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
}

procedure sumIsGreater0RealSum(this:Ref)  returns (r:bool)
{
	r:= (sum[this] > 0.0);
}
