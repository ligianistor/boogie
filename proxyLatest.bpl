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
requires fracBasicFieldsRealSum[this] > 0.0;
ensures (sum[this] == s1) && (n[this]==n1);

procedure PackSumOKRealSum(s1:real, n1:int, this:Ref);
requires (packedSumOKRealSum[this] == false);
requires (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure UnpackSumOKRealSum(s1:real, n1:int, this:Ref);
requires packedSumOKRealSum[this];
requires fracSumOKRealSum[this] > 0.0;
ensures (sum[this] == s1) && (n[this]==n1) &&
	( s1 == n1 * (n1+1) / 2 );

procedure PackSumGreater0RealSum(s1:real, this:Ref);
requires (packedSumGreater0RealSum[this] == false);
requires (sum[this] == s1) && (s1 > 0.0);

procedure UnpackSumGreater0RealSum(s1:real, this:Ref);
requires packedSumGreater0RealSum[this];
requires fracSumGreater0RealSum[this] > 0.0;
ensures (sum[this] == s1) && (s1 > 0.0);

procedure ConstructRealSum(n1:int, s:Ref, this:Ref);
ensures n[this] == n1;
ensures sum[this] == s;

procedure calculateRealSum(n1:int, this:Ref) returns (r:real)
modifies sum;
requires packedBasicFieldsRealSum[this] && (fracBasicFieldsRealSum[this] == 1.0);
ensures packedSumOKRealSum[this] && (fracSumOKRealSum[this]==1.0);
{
	sum[this] := n1 * (n1 + 1) / 2;
	r := sum[this];
}

procedure calculateSumRealSum(n1:int, this:Ref)  returns (r:real)
modifies n, sum;
requires packedBasicFieldsRealSum[this] && (fracBasicFieldsRealSum[this] == 1.0);
ensures packedSumOKRealSum[this] && (fracSumOKRealSum[this] == 1.0);

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

//---------------------

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

//------------------------------------

var sumClient : [Ref]Ref;
var instanceof: [Ref]int; // maybe this should be declared in the interface Sum
// actually it's ok to be declared in the first class that implements the interface because
// that way I don't need to translate the interface.

var packedClientSumOK : [Ref]bool;
var fracClientSumOK : [Ref]real;
var packedClientSumGreater0 : [Ref]bool;
var fracClientSumGreater0 : [Ref]real;

procedure PackClientSumOK(this:Ref);
requires (packedClientSumOK[this] == false);

procedure UnpackClientSumOK(this:Ref);
requires packedClientSumOK[this];
requires fracClientSumOK[this] > 0.0;

procedure PackClientSumGreater0(this:Ref);
requires (packedClientSumGreater0[this] == false);

procedure UnpackClientSumGreater0(this:Ref);
requires packedClientSumGreater0[this];
requires fracClientSumGreater0[this] > 0.0;

procedure ConstructClientSum(sum1:Ref, this:Ref);
ensures sumClient[this] == sum1;

procedure checkSumIsOK(this:Ref) returns (r:bool)
requires (instanceof[sumClient[this]] == 1) ==> 
	((fracSumOKProxySum[sumClient[this]] == 1.0) &&
         packedSumOKProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumOKRealSum[sumClient[this]] == 1.0) &&
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
	((fracSumGreater0ProxySum[sumClient[this]] == 1.0) &&
         packedSumGreater0ProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumGreater0RealSum[sumClient[this]] == 1.0) &&
         packedSumGreater0RealSum[sumClient[this]]);
{
if (instanceof[sumClient[this]] == 1) {
call r:=sumIsGreater0ProxySum(sumClient[this]);
} else {
call r:=sumIsGreater0RealSum(sumClient[this]);
}
}

procedure main(this:Ref) 
{
var s,s2:Ref;
var client1, client2:Ref;
var client3, client4:Ref;
var temp : real;
var temp1 : real;
var temp2 : bool;

assume (forall y:Ref :: (fracSumOKProxySum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0ProxySum[y] >= 0.0) );

assume (forall y:Ref :: (fracSumOKRealSum[y] >= 0.0) );
assume (forall y:Ref :: (fracSumGreater0RealSum[y] >= 0.0) );

call ConstructProxySum(0,0,s);
packedSumOKProxySum[s] := false;
call PackSumOKProxySum(sum[s],n[s],s);
packedSumOKProxySum[s] := true;
fracSumOKProxySum[s] := 1.0;

call ConstructClientSum(s, client1);
packedClientSumOK[client1] := false;
call PackClientSumOK(client1);
packedClientSumOK[client1] := true;
fracClientSumOK[client1] := 1.0;

call ConstructClientSum(s, client2);
packedClientSumOK[client2] := false;
call PackClientSumOK(client2);
packedClientSumOK[client2] := true;
fracClientSumOK[client2] := 1.0;

if (instanceof[s] == 1) {
	call temp := calculateSumProxySum(5,s);
} else {
	call temp := calculateSumRealSum(5,s);
}

call temp2 := checkSumIsOK(client1);

if (instanceof[s] == 1) {
	call temp := calculateSumProxySum(5,s);
} else {
	call temp := calculateSumRealSum(5,s);
}

call temp2 := checkSumIsOK(client2);

//------

call ConstructProxySum(0,0,s2);
packedSumGreater0ProxySum[s2] := false;
call PackSumGreater0ProxySum(sum[s2],s2);
packedSumGreater0ProxySum[s2] := true;
fracSumGreater0ProxySum[s2] := 1.0;

call ConstructClientSum(s2, client3);
packedClientSumGreater0[client3] := false;
call PackClientSumGreater0(client3);
packedClientSumGreater0[client3] := true;
fracClientSumGreater0[client3] := 1.0;

call ConstructClientSum(s2, client4);
packedClientSumGreater0[client4] := false;
call PackClientSumGreater0(client4);
packedClientSumGreater0[client4] := true;
fracClientSumGreater0[client4] := 1.0;

if (instanceof[s2] == 1) {
	call temp1 := calculateSumProxySum(7,s2);
} else {
	call temp1 := calculateSumRealSum(7,s2);
}

call temp2 := checkSumGreater0(client3);

if (instanceof[s2] == 1) {
	call temp1 := calculateSumProxySum(7,s2);
} else {
	call temp1 := calculateSumRealSum(7,s2);
}

call temp2 := checkSumGreater0(client4);

}

