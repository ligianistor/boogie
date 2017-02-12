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
requires (instanceof[suCli] == 1) ==> (fracSumOKProxySum[suCli] > 0.0) ;
requires (instanceof[suCli] == 2) ==> (fracSumOKRealSum[suCli] > 0.0) ;

procedure UnpackClientSumOK(suCli:Ref, this:Ref);
requires packedClientSumOK[this];
requires fracClientSumOK[this] > 0.0;
ensures sumClient[this] == suCli;
// TODO add requires about parameters if needed
ensures (instanceof[suCli] == 1) ==> (fracSumOKProxySum[suCli] > 0.0) ;
ensures (instanceof[suCli] == 2) ==> (fracSumOKRealSum[suCli] > 0.0) ;

procedure PackClientSumGreater0(suCli:Ref, this:Ref);
requires (packedClientSumGreater0[this] == false);
requires sumClient[this] == suCli;
// TODO add requires about parameters if needed
requires (instanceof[suCli] == 1) ==> (fracSumGreater0ProxySum[suCli] > 0.0) ;
requires (instanceof[suCli] == 2) ==> (fracSumGreater0RealSum[suCli] > 0.0) ;

procedure UnpackClientSumGreater0(suCli:Ref, this:Ref);
requires packedClientSumGreater0[this];
requires fracClientSumGreater0[this] > 0.0;
ensures sumClient[this] == suCli;
// TODO add requires about parameters if needed
ensures (instanceof[suCli] == 1) ==> (fracSumGreater0ProxySum[suCli] > 0.0) ;
ensures (instanceof[suCli] == 2) ==> (fracSumGreater0RealSum[suCli] > 0.0) ;

procedure ConstructClientSum(sum1:Ref, this:Ref)
modifies sumClient,  packedSumOKRealSum;
ensures sumClient[this] == sum1;
ensures (forall y:Ref :: ( (y!=this) ==> (sumClient[y] == old(sumClient[y]) ) ) );
{
	sumClient[this] := sum1;
}

procedure checkSumIsOK(this:Ref) returns (r:bool)
modifies packedSumOKRealSum, packedSumOKProxySum;
requires packedClientSumOK[this] == false;
requires fracClientSumOK[this] > 0.0;
requires (instanceof[sumClient[this]] == 1) ==> 
	((fracSumOKProxySum[sumClient[this]] > 0.0) &&
         packedSumOKProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumOKRealSum[sumClient[this]] > 0.0) &&
         packedSumOKRealSum[sumClient[this]]);
ensures (instanceof[sumClient[this]] == 1) ==> 
	((fracSumOKProxySum[sumClient[this]] > 0.0) &&
         packedSumOKProxySum[sumClient[this]] );
ensures (instanceof[sumClient[this]] == 2)==> 
	((fracSumOKRealSum[sumClient[this]] > 0.0) &&
         packedSumOKRealSum[sumClient[this]]);
ensures packedClientSumOK[this] == false;
ensures fracClientSumOK[this] > 0.0;
{
if (instanceof[sumClient[this]] == 1) {
call r := sumIsOKProxySum(sumClient[this]);
} else if (instanceof[sumClient[this]] == 2){
call r := sumIsOKRealSum(sumClient[this]);
} else {
  // we cannot get into this branch
  assume false;
}

}

procedure checkSumGreater0(this:Ref) returns (r:bool)
modifies packedSumGreater0RealSum, packedSumGreater0ProxySum;
requires packedClientSumGreater0[this] == false;
requires fracClientSumGreater0[this] > 0.0;
requires (instanceof[sumClient[this]] == 1) ==> 
	((fracSumGreater0ProxySum[sumClient[this]] > 0.0) &&
         packedSumGreater0ProxySum[sumClient[this]] );
requires (instanceof[sumClient[this]] == 2)==> 
	((fracSumGreater0RealSum[sumClient[this]] > 0.0) &&
         packedSumGreater0RealSum[sumClient[this]]);
ensures (instanceof[sumClient[this]] == 1) ==> 
	((fracSumGreater0ProxySum[sumClient[this]] > 0.0) &&
         packedSumGreater0ProxySum[sumClient[this]] );
ensures (instanceof[sumClient[this]] == 2)==> 
	((fracSumGreater0RealSum[sumClient[this]] > 0.0) &&
         packedSumGreater0RealSum[sumClient[this]]);
ensures packedClientSumGreater0[this] == false;
ensures fracClientSumGreater0[this] > 0.0;
{
if (instanceof[sumClient[this]] == 1) {
call r:=sumIsGreater0ProxySum(sumClient[this]);
} else if (instanceof[sumClient[this]] == 2) {
call r:=sumIsGreater0RealSum(sumClient[this]);
} else {
  // we cannot get into this branch
  assume false;
}
}

procedure main1(this:Ref) 
modifies packedSumOKProxySum, fracSumOKProxySum, 
    packedClientSumOK, fracClientSumOK, sum, n,
     realSum, sumClient, packedSumOKRealSum, fracSumOKRealSum, 
     packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedBasicFieldsProxySum,
     fracBasicFieldsProxySum, instanceof;
{
var s:Ref;
var client1, client2:Ref;
var temp : real;
var temp1 : real;
var temp2 : bool;

assume(client1!=client2);

assume (forall y:Ref :: (fracSumOKProxySum[y] >= 0.0) );

assume (forall y:Ref :: (fracSumOKRealSum[y] >= 0.0) );

call ConstructProxySum(5,s);
packedBasicFieldsProxySum[s] := false;
call PackBasicFieldsProxySum(realSum[s], sum[s], n[s], s);
packedBasicFieldsProxySum[s] := true;
fracBasicFieldsProxySum[s] := 1.0;
instanceof[s] := 1;
// could keep the if like below
// but I instead simplified it

call UnpackBasicFieldsProxySum(realSum[s], sum[s], n[s], s);
packedBasicFieldsProxySum[s] := false;

call temp := calculateSumProxySum(s);

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

call UnpackClientSumOK(s, client1);
packedClientSumOK[client1] := false;
call temp2 := checkSumIsOK(client1);

//transfer from one object proposition to another
packedBasicFieldsProxySum[s] := packedSumOKProxySum[s];
fracBasicFieldsProxySum[s] := fracSumOKProxySum[s];

call UnpackBasicFieldsProxySum(realSum[s], sum[s], n[s], s);
packedBasicFieldsProxySum[s] := false;
call temp := calculateSumProxySum(s);

call UnpackClientSumOK(s, client2);
packedClientSumOK[client2] := false;

call temp2 := checkSumIsOK(client2);
}


procedure main2(this:Ref) 
modifies  sum,
     packedSumGreater0ProxySum, fracSumGreater0ProxySum,
     packedClientSumGreater0, fracClientSumGreater0, n,
     realSum, sumClient, packedBasicFieldsRealSum, packedSumOKRealSum, fracSumOKRealSum,
     fracBasicFieldsRealSum, packedBasicFieldsProxySum,
     fracBasicFieldsProxySum, packedSumGreater0RealSum, fracSumGreater0RealSum,
     instanceof;
{
var s2:Ref;
var client3, client4:Ref;
var temp : real;
var temp1 : real;
var temp2 : bool;

assume(client3!=client4);

assume (forall y:Ref :: (fracSumGreater0ProxySum[y] >= 0.0) );

assume (forall y:Ref :: (fracSumGreater0RealSum[y] >= 0.0) );

call ConstructProxySum(7,s2);
packedBasicFieldsProxySum[s2] := false;
call PackBasicFieldsProxySum(realSum[s2], sum[s2], n[s2], s2);
packedBasicFieldsProxySum[s2] := true;
fracBasicFieldsProxySum[s2] := 1.0;
instanceof[s2] := 1;

call UnpackBasicFieldsProxySum(realSum[s2], sum[s2], n[s2], s2);
packedBasicFieldsProxySum[s2] := false;
call temp1 := addOneToSumProxySum(s2);

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

call UnpackClientSumGreater0(s2, client3);
packedClientSumGreater0[client3] := false;

call temp2 := checkSumGreater0(client3);

//transfer from one object proposition to another
packedBasicFieldsProxySum[s2] := packedSumGreater0ProxySum[s2];
fracBasicFieldsProxySum[s2] := fracSumGreater0ProxySum[s2];

call UnpackBasicFieldsProxySum(realSum[s2], sum[s2], n[s2], s2);
packedBasicFieldsProxySum[s2] := false;
call temp1 := addOneToSumProxySum(s2);

call UnpackClientSumGreater0(s2, client4);
packedClientSumGreater0[client4] := false;

call temp2 := checkSumGreater0(client4);
}
