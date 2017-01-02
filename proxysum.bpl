var packedSumOKProxySum: [Ref] bool;
var fracSumOKProxySum: [Ref] real;
var packedSumGreater0ProxySum: [Ref] bool;
var fracSumGreater0ProxySum: [Ref] real;
var packedBasicFieldsProxySum: [Ref] bool;
var fracBasicFieldsProxySum: [Ref] real;

var realSum: [Ref]Ref;

procedure PackBasicFieldsProxySum(s1:real, n1:int, this:Ref);
requires (packedBasicFieldsProxySum[this] == false);
requires (sum[this] == s1) && (n[this]==n1);

procedure UnpackBasicFieldsProxySum(s1:real, n1:int, this:Ref);
requires packedBasicFieldsProxySum[this];
requires fracBasicFieldsProxySum[this] > 0.0;
ensures (sum[this] == s1) && (n[this]==n1);

procedure PackSumOKProxySum(s1:real, n1:int, this:Ref);
requires (packedSumOKProxySum[this] == false);
requires (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure UnpackSumOKProxySum(s1:real, n1:int, this:Ref);
requires packedSumOKProxySum[this];
requires fracSumOKProxySum[this] > 0.0;
ensures (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure PackSumGreater0ProxySum(s1:real, this:Ref);
requires (packedSumGreater0ProxySum[this] == false);
requires (sum[this] == s1) && (s1 > 0.0);

procedure UnpackSumGreater0ProxySum(s1:real, this:Ref);
requires packedSumGreater0ProxySum[this];
requires fracSumGreater0ProxySum[this] > 0.0;
ensures (sum[this] == s1) && (s1 > 0.0);

procedure ConstructProxySum(n1:int, s1:Ref, this:Ref);
ensures n[this] == n1;
ensures sum[this] == s1;

procedure calculateSumProxySum(n1:int, this:Ref)  returns (r:real)
modifies n,sum;
{ 
  var temp : real;
n[this]:=n1;
if (realSum[this]==null) {
	call sumConstrRealSum(n[this], realSum[this]);
}

	call temp := calculateSumRealSum(realSum[this]);
  	sum[this]:=temp;
	r:=sum[this];
}

procedure sumIsOKProxySum(this:Ref) returns (r:bool) {
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
}

procedure sumIsGreater0ProxySum(this:Ref)  returns (r:bool)
{
	r:= (sum[this] > 0.0);
}
