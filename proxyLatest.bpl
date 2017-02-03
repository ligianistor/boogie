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

procedure UnpackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires packedBasicFieldsRealSum[this];
requires fracBasicFieldsRealSum[this] > 0.0;
ensures	(n[this]==n1);
ensures (sum[this] == su);

procedure PackSumOKRealSum(n1:int, this:Ref);
requires (packedSumOKRealSum[this] == false);
requires (n[this]==n1);
requires ( sum[this] == (n1 * (n1+1) / 2) );

procedure UnpackSumOKRealSum(n1:int, this:Ref);
requires packedSumOKRealSum[this];
requires fracSumOKRealSum[this] > 0.0;
ensures	(n[this]==n1);
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
{
  	var temp:real;
	n[this] := n1;
  sum[this] := 0.0;
  packedBasicFieldsRealSum[this] := false;
  call PackBasicFieldsRealSum(0.0, n1, this);
  packedBasicFieldsRealSum[this] := true;
  fracBasicFieldsRealSum[this] := 1.0;
	call temp := calculateRealSum(this);
}

procedure addOneToSumRealSum(n1: int, this:Ref)
modifies n, sum, packedSumGreater0RealSum, packedSumOKRealSum,
        fracSumOKRealSum;
requires n1 > 0;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] == 1.0);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] == 1.0);
{
	var temp:real;
	n[this] := n1;
	call temp := calculateRealSum(this);
  call UnpackSumOKRealSum(n[this], this);
  packedSumOKRealSum[this] := false;
	sum[this] := temp+1.0;
  packedSumGreater0RealSum[this] := packedSumOKRealSum[this];
  call PackSumGreater0RealSum(sum[this], this);
  packedSumGreater0RealSum[this]:=true;
}

procedure calculateSumRealSum(this:Ref)  returns (r:real)
modifies sum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
ensures packedSumOKRealSum[this];
ensures	(fracSumOKRealSum[this] > 0.0);
{ 
	r := sum[this];
}

procedure calculateRealSum(this:Ref) returns (r:real)
modifies sum, packedSumOKRealSum, fracSumOKRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
requires n[this] > 0;
ensures packedSumOKRealSum[this];
ensures	(fracSumOKRealSum[this] > 0.0);
ensures sum[this] == (n[this]*(n[this]+1)/2);
ensures r > 0.0;
{
	sum[this] := n[this] * (n[this] + 1) / 2;
	r := sum[this];
  call PackSumOKRealSum(n[this], this);
  packedSumOKRealSum[this] := true;
  // I transfer the fraction from one predicate to the other
  fracSumOKRealSum[this] := fracBasicFieldsRealSum[this];
}


procedure sumIsOKRealSum( this:Ref) returns (r:bool) 
requires packedSumOKRealSum[this];
requires (fracSumOKRealSum[this] > 0.0);
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
{
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
}

procedure sumIsGreater0RealSum(this:Ref)  returns (r:bool)
requires packedSumGreater0RealSum[this];
requires (fracSumGreater0RealSum[this] > 0.0);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
{
	r:= (sum[this] > 0.0);
}

//---------------------

var packedSumOKProxySum: [Ref] bool;
var fracSumOKProxySum: [Ref] real;
var packedSumGreater0ProxySum: [Ref] bool;
var fracSumGreater0ProxySum: [Ref] real;
var packedBasicFieldsProxySum: [Ref] bool;
var fracBasicFieldsProxySum: [Ref] real;

var realSum: [Ref]Ref;

procedure PackBasicFieldsProxySum(su:real, n1:int, this:Ref);
requires (packedBasicFieldsProxySum[this] == false);
requires (n[this] == n1);
requires (sum[this] == su);

procedure UnpackBasicFieldsProxySum(su:real, n1:int, this:Ref);
requires packedBasicFieldsProxySum[this];
requires fracBasicFieldsProxySum[this] > 0.0;
ensures	(n[this] == n1);
ensures (sum[this] == su);

procedure PackSumOKProxySum(n1:int, this:Ref);
requires (packedSumOKProxySum[this] == false);
requires (n[this] == n1) && ( sum[this] == n1 * (n1+1) / 2 );

procedure UnpackSumOKProxySum(n1:int, this:Ref);
requires packedSumOKProxySum[this];
requires fracSumOKProxySum[this] > 0.0;
ensures	(n[this] == n1);
ensures (sum[this] == (n1 * (n1+1) / 2));

procedure PackSumGreater0ProxySum(s1:real, this:Ref);
requires (packedSumGreater0ProxySum[this] == false);
requires (sum[this] == s1) && (s1 > 0.0);

procedure UnpackSumGreater0ProxySum(s1:real, this:Ref);
requires packedSumGreater0ProxySum[this];
requires fracSumGreater0ProxySum[this] > 0.0;
ensures (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructProxySum(n1:int, this:Ref)
modifies n, sum, realSum;
ensures n[this] == n1;
ensures sum[this] == (n1*(n1+1)/2);
{
	n[this] := n1;
	sum[this] := 0.0;
	realSum[this] := null;
}

procedure calculateSumProxySum(this:Ref)  returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum
      , packedBasicFieldsRealSum, fracBasicFieldsRealSum;
requires packedBasicFieldsProxySum[this];
requires (fracBasicFieldsProxySum[this] > 0.0);
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
	call temp := calculateSumRealSum(this);
  	sum[this]:=temp;
	  r:=sum[this];
}

procedure addOneToSumProxySum(n1:int, this:Ref)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum
        , packedBasicFieldsRealSum, fracBasicFieldsRealSum,
        packedSumGreater0RealSum;
requires packedBasicFieldsProxySum[this];
requires (fracBasicFieldsProxySum[this] == 1.0);
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] == 1.0);
{
	n[this] := n1;
	
	if (realSum[this] == null) {
		call ConstructRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := false;
		call PackSumOKRealSum(n[this], realSum[this]);
		packedSumOKRealSum[realSum[this]] := true;
		fracSumOKRealSum[realSum[this]] := 1.0;
	} 
	call addOneToSumRealSum(n[this], realSum[this]) ;
}

procedure sumIsOKProxySum(this:Ref) returns (r:bool)
requires packedSumOKProxySum[this];
requires (fracSumOKProxySum[this] > 0.0);
ensures packedSumOKProxySum[this];
ensures (fracSumOKProxySum[this] > 0.0); {
	r := (sum[this] == (n[this] * (n[this]+1) / 2.0));
}

procedure sumIsGreater0ProxySum(this:Ref)  returns (r:bool)
requires packedSumGreater0ProxySum[this];
requires (fracSumGreater0ProxySum[this] > 0.0);
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] > 0.0);
{
	r:= (sum[this] > 0.0);
}

//------------------------------------

var sumClient : [Ref]Ref;
var instanceof: [Ref]int; // maybe this should be declared in the interface Sum
// actually it's ok to be declared in the first class that implements the interface because
// that way I don't need to translate the interface.

var packedClientSumOK : [Ref]bool;
var fracClientSumOK : [Ref]real;
var packedClientSumGreater0 : [Ref]bool;
var fracClientSumGreater0 : [Ref]real;

procedure PackClientSumOK(suCli:Ref, this:Ref);
requires (packedClientSumOK[this] == false);
requires sumClient[this] == suCli;
// TODO add requires about parameters if needed
requires fracClientSumOK[suCli] > 0.0;

procedure UnpackClientSumOK(suCli:Ref, this:Ref);
requires packedClientSumOK[this];
requires fracClientSumOK[this] > 0.0;
ensures sumClient[this] == suCli;
// TODO add requires about parameters if needed
ensures fracClientSumOK[suCli] > 0.0;

procedure PackClientSumGreater0(suCli:Ref, this:Ref);
requires (packedClientSumGreater0[this] == false);
requires sumClient[this] == suCli;
// TODO add requires about parameters if needed
requires fracClientSumGreater0[suCli] > 0.0;

procedure UnpackClientSumGreater0(suCli:Ref, this:Ref);
requires packedClientSumGreater0[this];
requires fracClientSumGreater0[this] > 0.0;
ensures sumClient[this] == suCli;
// TODO add requires about parameters if needed
ensures fracClientSumGreater0[suCli] > 0.0;

procedure ConstructClientSum(sum1:Ref, this:Ref)
modifies sumClient;
ensures sumClient[this] == sum1;
{
	sumClient[this] := sum1;
}

procedure checkSumIsOK(this:Ref) returns (r:bool)
requires (instanceof[sumClient[this]] == 1) ==> 
	((fracSumOKProxySum[sumClient[this]] > 0.0) &&
         packedSumOKProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumOKRealSum[sumClient[this]] > 0.0) &&
         packedSumOKRealSum[sumClient[this]]);
{
if (instanceof[sumClient[this]] == 1) {
call r:=sumIsOKProxySum(sumClient[this]);
} else {
call r:=sumIsOKRealSum(sumClient[this]);
}

}

procedure checkSumGreater0(this:Ref) returns (r:bool)
requires (instanceof[sumClient[this]] == 1) ==> 
	((fracSumGreater0ProxySum[sumClient[this]] > 0.0) &&
         packedSumGreater0ProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumGreater0RealSum[sumClient[this]] > 0.0) &&
         packedSumGreater0RealSum[sumClient[this]]);
{
if (instanceof[sumClient[this]] == 1) {
call r:=sumIsGreater0ProxySum(sumClient[this]);
} else {
call r:=sumIsGreater0RealSum(sumClient[this]);
}
}

procedure main1(this:Ref) 
modifies packedSumOKProxySum, fracSumOKProxySum, 
    packedClientSumOK, fracClientSumOK, sum,
     packedSumGreater0ProxySum, fracSumGreater0ProxySum,
     packedClientSumGreater0, fracClientSumGreater0, n,
     realSum, sumClient, packedSumOKRealSum, fracSumOKRealSum
     , packedBasicFieldsRealSum, fracBasicFieldsRealSum;
{
var s:Ref;
var client1, client2:Ref;
var temp : real;
var temp1 : real;
var temp2 : bool;

assume (forall y:Ref :: (fracSumOKProxySum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0ProxySum[y] >= 0.0) );

assume (forall y:Ref :: (fracSumOKRealSum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0RealSum[y] >= 0.0) );

call ConstructProxySum(5,s);
packedSumOKProxySum[s] := false;
call PackSumOKProxySum(n[s],s);
packedSumOKProxySum[s] := true;
fracSumOKProxySum[s] := 1.0;

call ConstructClientSum(s, client1);
packedClientSumOK[client1] := false;
call PackClientSumOK(s, client1);
packedClientSumOK[client1] := true;
fracClientSumOK[client1] := 1.0;

call ConstructClientSum(s, client2);
packedClientSumOK[client2] := false;
call PackClientSumOK(s, client2);
packedClientSumOK[client2] := true;
fracClientSumOK[client2] := 1.0;

if (instanceof[s] == 1) {
	call temp := calculateSumProxySum(s);
} else {
	call temp := calculateSumRealSum(s);
}

call temp2 := checkSumIsOK(client1);

if (instanceof[s] == 1) {
	call temp := calculateSumProxySum(s);
} else {
	call temp := calculateSumRealSum(s);
}

call temp2 := checkSumIsOK(client2);
}


procedure main2(this:Ref) 
modifies packedSumOKProxySum, fracSumOKProxySum, 
    packedClientSumOK, fracClientSumOK, sum,
     packedSumGreater0ProxySum, fracSumGreater0ProxySum,
     packedClientSumGreater0, fracClientSumGreater0, n,
     realSum, sumClient, packedSumOKRealSum, fracSumOKRealSum
     , packedBasicFieldsRealSum, fracBasicFieldsRealSum;
{
var s2:Ref;
var client3, client4:Ref;
var temp : real;
var temp1 : real;
var temp2 : bool;

assume (forall y:Ref :: (fracSumOKProxySum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0ProxySum[y] >= 0.0) );

assume (forall y:Ref :: (fracSumOKRealSum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0RealSum[y] >= 0.0) );

call ConstructProxySum(7,s2);
packedSumGreater0ProxySum[s2] := false;
call PackSumGreater0ProxySum(sum[s2],s2);
packedSumGreater0ProxySum[s2] := true;
fracSumGreater0ProxySum[s2] := 1.0;

call ConstructClientSum(s2, client3);
packedClientSumGreater0[client3] := false;
call PackClientSumGreater0(s2, client3);
packedClientSumGreater0[client3] := true;
fracClientSumGreater0[client3] := 1.0;

call ConstructClientSum(s2, client4);
packedClientSumGreater0[client4] := false;
call PackClientSumGreater0(s2, client4);
packedClientSumGreater0[client4] := true;
fracClientSumGreater0[client4] := 1.0;

if (instanceof[s2] == 1) {
	call temp1 := calculateSumProxySum(s2);
} else {
	call temp1 := calculateSumRealSum(s2);
}

call temp2 := checkSumGreater0(client3);

if (instanceof[s2] == 1) {
	call temp1 := calculateSumProxySum(s2);
} else {
	call temp1 := calculateSumRealSum(s2);
}

call temp2 := checkSumGreater0(client4);
}



