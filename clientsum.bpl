var sumClient : [Ref]Ref;
var instanceof: [Ref]int;

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

procedure main() 
{
var s,s2:Ref;
var client1, client2:Ref;
var client3, client4:Ref;
call ConstructProxySum(5,s);
call 
	Sum s = new ProxySum(sumOK()[])(5);
	ClientSum client1 = new ClientSum(s);
	ClientSum client2 = new ClientSum(s);
	s.calculateSum();
	client1.checkSumIsOK();
	s.calculateSum();
	client2.checkSumIsOK();

	Sum s2 = new ProxySum(sumGreater0()[])(7);
	ClientSum client3 = new ClientSum(s2);
	ClientSum client4 = new ClientSum(s2);
	s2.calculateSum();
	client3.checkSumGreater0();
	s2.calculateSum();
	client4.checkSumGreater0();
}

