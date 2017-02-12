type Ref;
var packedBasicFieldsRealSum: [Ref] bool;
var fracBasicFieldsRealSum: [Ref] real;
var packedSumOKRealSum: [Ref] bool;
var fracSumOKRealSum: [Ref] real;
var packedSumGreater0RealSum: [Ref] bool;
var fracSumGreater0RealSum: [Ref] real;

const null: Ref;

var n: [Ref]int;
// sum can be considerent a dependent field on n
var sum: [Ref]real;

procedure PackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires (packedBasicFieldsRealSum[this] == false);
requires (n[this]==n1);
requires (sum[this] == su);
requires n1 > 0;

procedure UnpackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires packedBasicFieldsRealSum[this];
requires fracBasicFieldsRealSum[this] > 0.0;
ensures	(n[this]==n1);
ensures (sum[this] == su);
ensures n1 > 0;

procedure PackSumOKRealSum(n1:int, this:Ref);
requires (packedSumOKRealSum[this] == false);
requires (n[this]==n1);
requires n1 > 0;
requires ( sum[this] == (n1 * (n1+1) / 2) );

procedure UnpackSumOKRealSum(n1:int, this:Ref);
requires packedSumOKRealSum[this];
requires fracSumOKRealSum[this] > 0.0;
ensures	(n[this]==n1);
ensures n1 > 0;
ensures	(sum[this] == (n1 * (n1+1) / 2) );

procedure PackSumGreater0RealSum(s1:real, this:Ref);
requires (packedSumGreater0RealSum[this] == false);
requires (sum[this] == s1);
requires (s1 > 0.0);

procedure UnpackSumGreater0RealSum(s1:real, this:Ref);
requires packedSumGreater0RealSum[this];
requires fracSumGreater0RealSum[this] > 0.0;
ensures (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructRealSum(n1:int, this:Ref)
modifies n, sum, packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedSumOKRealSum,
        fracSumOKRealSum;
requires n1 > 0;
ensures n[this] == n1;
ensures sum[this] == (n1*(n1+1)/2);
// since the constructors also have a body now, they ensures forall like the other
// procedures
ensures (forall y:Ref :: ( (y!=this) ==> (n[y] == old(n[y]) ) ) );
{
  	var temp:real;
	n[this] := n1;
  sum[this] := 0.0;
 // same sequence of statements below like when calling constructors
 // because we have no object propositions yet as we are inside a constructor here
  packedBasicFieldsRealSum[this] := false;
  call PackBasicFieldsRealSum(0.0, n1, this);
  packedBasicFieldsRealSum[this] := true;
  fracBasicFieldsRealSum[this] := 1.0;
	call temp := calculateRealSum(this);
}

procedure addOneToSumRealSum(this:Ref) returns (r:real)
modifies n, sum, packedSumGreater0RealSum, packedSumOKRealSum,
        fracSumOKRealSum, fracSumGreater0RealSum, packedBasicFieldsRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
//result becomes a keyword in Oprop to refer to the return result of this procedure
ensures r > 0.0;
{
	var temp : real;
	call temp := calculateRealSum(this);
	sum[this] := temp + 1.0;
//transfer from one object proposition to another
//transfer becomes an object proposition in Oprop
  packedSumGreater0RealSum[this] := packedSumOKRealSum[this];
  fracSumGreater0RealSum[this] := fracSumOKRealSum[this];

  call PackSumGreater0RealSum(sum[this], this);
  packedSumGreater0RealSum[this] := true;
  r := sum[this];
}

// calculateSumRealSum() and calculateSumProxySum() will
// have stronger object propositions as pre-conditions
// but they have to have at least the pre-conditions that calculateSum()
// has in the interface.
procedure calculateSumRealSum(this:Ref)  returns (r:real)
modifies sum, packedSumOKRealSum;
requires packedSumOKRealSum[this];
requires (fracSumOKRealSum[this] > 0.0);
// TODO should instead return an object and write an object proposition 
// that respects modularity for that object
ensures r == (n[this]*(n[this]+1)/2);
ensures packedSumOKRealSum[this] == false;
ensures (fracSumOKRealSum[this] > 0.0);
ensures (n[this] > 0);
{ 
  call UnpackSumOKRealSum(n[this], this);
  packedSumOKRealSum[this] := false;
	r := sum[this];
}

procedure calculateRealSum(this:Ref) returns (r:real)
modifies sum, packedSumOKRealSum, fracSumOKRealSum, packedBasicFieldsRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
ensures r > 0.0;
ensures sum[this] == (n[this]*(n[this]+1)/2);
ensures (packedSumOKRealSum[this] == false);
ensures (fracSumOKRealSum[this] > 0.0);
//ensures (forall y:Ref :: ( (y!=this) ==> (fracSumOKRealSum[y] == old(fracSumOKRealSum[y]) ) ) );
{
  call UnpackBasicFieldsRealSum(sum[this], n[this], this);
  packedBasicFieldsRealSum[this] := false;
	sum[this] := n[this] * (n[this] + 1) / 2;
	r := sum[this];
  
   // I transfer the fraction from one predicate to the other
  packedSumOKRealSum[this] := packedBasicFieldsRealSum[this];
  fracSumOKRealSum[this] := fracBasicFieldsRealSum[this];
}


procedure sumIsOKRealSum( this:Ref) returns (r:bool) 
modifies packedSumOKRealSum;
requires packedSumOKRealSum[this];
requires (fracSumOKRealSum[this] > 0.0);
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
{
	call UnpackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := false;
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
	call PackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := true;
}

procedure sumIsGreater0RealSum(this:Ref)  returns (r:bool)
modifies packedSumGreater0RealSum;
requires packedSumGreater0RealSum[this];
requires (fracSumGreater0RealSum[this] > 0.0);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
{
	call UnpackSumGreater0RealSum(sum[this], this);
	packedSumGreater0RealSum[this] := false;
	r:= (sum[this] > 0.0);
	call PackSumGreater0RealSum(sum[this], this);
	packedSumGreater0RealSum[this] := true;
}

