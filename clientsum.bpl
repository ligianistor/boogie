var sumClient : [Ref]Ref;
var instanceof: [Ref]int; // maybe this should be declared in the interface Sum

var packedClientSumOK : [Ref]bool;
var fracClientSumOK : [Ref]real;
var packedClientSumGreater0 : [Ref]bool;
var fracClientSumGreater0 : [Ref]real;

procedure PackClientSumOK(this:Ref);
requires (packedClientSumOK[this] == false);

procedure UnpackClientSumOK(this:Ref);
requires packedClientSumOK[this];

procedure PackClientSumGreater0(this:Ref);
requires (packedClientSumGreater0[this] == false);

procedure UnpackClientSumGreater0(this:Ref);
requires packedClientSumGreater0[this];

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

call ConstructProxySum(s);
call sumConstrProxySum(5, s);
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

//------

call ConstructProxySum(s2);
call sumConstrProxySum(7, s2);
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

