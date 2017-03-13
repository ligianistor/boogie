
var packedSumOKProxySum: [Ref] bool;
var fracSumOKProxySum: [Ref] real;
var packedSumGreater0ProxySum: [Ref] bool;
var fracSumGreater0ProxySum: [Ref] real;
var packedBasicFieldsProxySum: [Ref] bool;
var fracBasicFieldsProxySum: [Ref] real;

var realSum: [Ref]Ref;

procedure PackBasicFieldsProxySum(rs:Ref, su:real, n1:int, this:Ref);
requires (packedBasicFieldsProxySum[this] == false);
requires (realSum[this] == rs);
requires (sum[this] == su);
requires (n[this] == n1);
requires (n1 > 0);

procedure UnpackBasicFieldsProxySum(rs:Ref, su:real, n1:int, this:Ref);
requires packedBasicFieldsProxySum[this];
requires fracBasicFieldsProxySum[this] > 0.0;
requires (realSum[this] == rs);
requires (sum[this] == su);
requires (n[this] == n1);
ensures (n1 > 0);

procedure PackSumOKProxySum(n1:int, this:Ref);
requires (packedSumOKProxySum[this] == false);
requires (n[this] == n1);
requires n1 > 0;
requires ( sum[this] == n1 * (n1+1) / 2 );

procedure UnpackSumOKProxySum(n1:int, this:Ref);
requires packedSumOKProxySum[this];
requires fracSumOKProxySum[this] > 0.0;
requires (n[this] == n1);
ensures n1 > 0;
ensures (sum[this] == (n1 * (n1+1) / 2));

procedure PackSumGreater0ProxySum(s1:real, this:Ref);
requires (packedSumGreater0ProxySum[this] == false);
requires (sum[this] == s1);
requires (s1 > 0.0);

procedure UnpackSumGreater0ProxySum(s1:real, this:Ref);
requires packedSumGreater0ProxySum[this];
requires fracSumGreater0ProxySum[this] > 0.0;
requires (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructProxySum(n1:int, this:Ref)
modifies n, sum, realSum;
ensures n[this] == n1;
ensures sum[this] == 0.0;
ensures (realSum[this] == null);
{
	n[this] := n1;
	sum[this] := 0.0;
	realSum[this] := null;
}

procedure calculateSumProxySum(this:Ref)  returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum
      , packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedBasicFieldsProxySum,
      packedSumOKProxySum, fracSumOKProxySum;
requires packedBasicFieldsProxySum[this] == false;
requires (fracBasicFieldsProxySum[this] > 0.0);
requires n[this] > 0;
requires (realSum[this]!=null) ==> ( packedSumOKRealSum[realSum[this]] && (fracSumOKRealSum[realSum[this]] > 0.0) && (n[realSum[this]] == n[this]) );
ensures packedSumOKProxySum[this];
ensures	(fracSumOKProxySum[this] > 0.0);
{ 
	var temp : real;
	if (realSum[this]==null) {
		call ConstructRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := false;
		call PackSumOKRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := true;
		fracSumOKRealSum[realSum[this]] := 1.0;
	}
	  call temp := calculateSumRealSum(realSum[this]);
  	sum[this] := temp;
    
    // transfer from one object proposition to another
    packedSumOKProxySum[this] := packedBasicFieldsProxySum[this];
    fracSumOKProxySum[this] := fracBasicFieldsProxySum[this];
    call PackSumOKProxySum(n[this], this);
    packedSumOKProxySum[this] := true;
	  r := sum[this];
}

procedure addOneToSumProxySum(this:Ref) returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum
        , packedBasicFieldsRealSum, fracBasicFieldsRealSum,
        packedSumGreater0RealSum, fracSumGreater0RealSum,
        packedSumGreater0ProxySum, packedBasicFieldsProxySum,
        fracSumGreater0ProxySum;
requires packedBasicFieldsProxySum[this]==false;
//Should this be 1.0 or 0.0 , in all the requires here?
//I think it should be > 0 because it is like calculateSum, where sumOK() is the invariant.
//Only here sumGreater0() is the invariant.
requires (fracBasicFieldsProxySum[this] > 0.0);
requires n[this] > 0;
requires (realSum[this]!=null) ==> ( packedBasicFieldsRealSum[realSum[this]] && (fracBasicFieldsRealSum[realSum[this]] > 0.0) && (n[realSum[this]] == n[this]));
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] > 0.0);
{
  var temp : real;
	if (realSum[this] == null) {
		call ConstructRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := false;
		call PackSumOKRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := true;
		fracSumOKRealSum[realSum[this]] := 1.0;
    // transfer one object proposition to another one
    // which is less than this one
    packedBasicFieldsRealSum[realSum[this]] := packedSumOKRealSum[realSum[this]];
    fracBasicFieldsRealSum[realSum[this]] := fracSumOKRealSum[realSum[this]];
	} 

  call temp := addOneToSumRealSum(realSum[this]);
  sum[this] := temp;
  // transfer from one object proposition to another
  packedSumGreater0ProxySum[this] := packedBasicFieldsProxySum[this];
  fracSumGreater0ProxySum[this] := fracBasicFieldsProxySum[this];
  call PackSumGreater0ProxySum(sum[this], this);
  packedSumGreater0ProxySum[this] := true;
  r := sum[this];
}

procedure sumIsOKProxySum(this:Ref) returns (r:bool)
modifies packedSumOKProxySum;
requires packedSumOKProxySum[this];
requires (fracSumOKProxySum[this] > 0.0);
ensures packedSumOKProxySum[this];
ensures (fracSumOKProxySum[this] > 0.0); 
{
	call UnpackSumOKProxySum(n[this], this);
	packedSumOKProxySum[this] := false;
	r := (sum[this] == (n[this] * (n[this]+1) / 2.0));
	call PackSumOKProxySum(n[this], this);
	packedSumOKProxySum[this] := true;
}

procedure sumIsGreater0ProxySum(this:Ref)  returns (r:bool)
modifies packedSumGreater0ProxySum;
requires packedSumGreater0ProxySum[this];
requires (fracSumGreater0ProxySum[this] > 0.0);
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] > 0.0);
{
	call UnpackSumGreater0ProxySum(sum[this], this);
	packedSumGreater0ProxySum[this] := false;
	r:= (sum[this] > 0.0);
	call PackSumGreater0ProxySum(sum[this], this);
	packedSumGreater0ProxySum[this] := true;
}

