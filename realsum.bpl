type Ref;
var packedBasicFieldsRealSum: [Ref] bool;
var fracBasicFieldsRealSum: [Ref] real;
var packedSumOKRealSum: [Ref] bool;
var fracSumOKRealSum: [Ref] real;
var packedSumGreater0RealSum: [Ref] bool;
var fracSumGreater0RealSum: [Ref] real;

const null: Ref;

var n: [Ref]int;
var sum: [Ref]real;

procedure PackBasicFieldsRealSum(s1:real, n1:int, this:Ref);
requires (packedBasicFieldsRealSum[this] == false);
requires (sum[this] == s1) && (n[this]==n1);

procedure UnpackBasicFieldsRealSum(s1:real, n1:int, this:Ref);
requires packedBasicFieldsRealSum[this];
ensures (sum[this] == s1) && (n[this]==n1);

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

procedure ConstructRealSum(n1:int, s:Ref, this:Ref);
ensures n[this] == n1;
ensures sum[this] == s;

procedure calculateRealSum(n1:int, this:Ref) returns (r:real)
modifies sum;
requires packedBasicFieldsRealSum[this] && fracBasicFieldsRealSum[this]==1.0
ensures packedSumOKRealSum[this] && fracSumOKRealSum[this]==1.0
{
	sum[this] := n1 * (n1 + 1) / 2;
	r := sum[this];
}

procedure calculateSumRealSum(n1:int, this:Ref)  returns (r:real)
modifies n, sum;
requires packedBasicFieldsRealSum[this] && fracBasicFieldsRealSum[this]==1.0
ensures packedSumOKRealSum[this] && fracSumOKRealSum[this]==1.0

{ 
        n[this]:=n1;
	call r:= calculateRealSum(n1, this);
}

procedure sumIsOKRealSum( this:Ref) returns (r:bool) {
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
}

procedure sumIsGreater0RealSum(this:Ref)  returns (r:bool)
{
	r:= (sum[this] > 0.0);
}
