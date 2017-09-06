//realsum.bpl
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

procedure PackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires (packedBasicFieldsRealSum[this] == false);
requires (n[this]==n1);
requires (sum[this] == su);
requires n1 > 0;

procedure UnpackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires packedBasicFieldsRealSum[this];
requires fracBasicFieldsRealSum[this] > 0.0;
requires (n[this]==n1);
requires (sum[this] == su);
ensures n1 > 0;

procedure PackSumOKRealSum(n1:int, this:Ref);
requires (packedSumOKRealSum[this] == false);
requires fracBasicFieldsRealSum[this] > 0.0;
requires (n[this]==n1);
requires (sum[this]==(n1 * (n1+1) / 2) );

procedure UnpackSumOKRealSum(n1:int, this:Ref);
requires packedSumOKRealSum[this];
requires fracSumOKRealSum[this] > 0.0;
requires (n[this]==n1);
ensures	(sum[this] == (n1 * (n1+1) / 2) );

procedure PackSumGreater0RealSum(n1:int, s1:real, this:Ref);
requires (packedSumGreater0RealSum[this] == false);
requires fracBasicFieldsRealSum[this] > 0.0;
requires (n[this]==n1);
requires (sum[this] == s1);
requires (s1 > 0.0);

procedure UnpackSumGreater0RealSum(n1:int, s1:real, this:Ref);
requires packedSumGreater0RealSum[this];
requires fracSumGreater0RealSum[this] > 0.0;
requires (n[this]==n1);
requires (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructRealSum(n1:int, this:Ref)
modifies n, sum, packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedSumOKRealSum,
        fracSumOKRealSum;
requires n1 > 0;
ensures packedSumOKRealSum[this];
ensures fracSumOKRealSum[this] == 1.0;
ensures n[this] == n1;
// since the constructors also have a body now, they ensures forall like the other
// procedures
ensures (forall y:Ref :: ( (y!=this) ==> (n[y] == old(n[y]) ) ) );
ensures (forall y:Ref :: ( (y!=this) ==> (sum[y] == old(sum[y]) ) ) );
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
  call temp := calculateSumRealSum(this);
}

procedure addOneToSumRealSum(n1:int, s1:real, this:Ref) returns (r:real)
modifies n, sum, packedSumGreater0RealSum, packedSumOKRealSum,
        fracSumOKRealSum, fracSumGreater0RealSum, packedBasicFieldsRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
requires (n[this] == n1);
requires (sum[this] == s1);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
ensures r > 0.0;
{
  var temp, temp2 : real;
  n[this] := n1;
  call temp := calculateSumRealSum(n1, s1, this);
  call UnpackSumOKRealSum(n1, this);
  packedSumOKRealSum[this] := false;
  sum[this] := temp + 1.0;
  temp2 := sum[this];
  call PackSumGreater0RealSum(n1, sum[this], this);
  packedSumGreater0RealSum[this] := true;
  r := sum[this];
}

procedure calculateSumRealSum(n1:int, s1:real, this:Ref) returns (r:real)
modifies sum, packedSumOKRealSum, fracSumOKRealSum, packedBasicFieldsRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
requires (n[this] == n1);
requires (sum[this] == s1);
ensures r > 0.0;
ensures n[this] == n1;
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
//ensures (forall y:Ref :: ( (y!=this) ==> (fracSumOKRealSum[y] == old(fracSumOKRealSum[y]) ) ) );
{
  call UnpackBasicFieldsRealSum(s1, n1, this);
  packedBasicFieldsRealSum[this] := false;
  sum[this] := n1 * (n1 + 1) / 2;
  r := sum[this];
  call PackBasicFieldsRealSum(n1 * (n1 + 1) / 2, n1, this);
  packedBasicFieldsRealSum[this] := true;
  
  call PackSumOKRealSum(n1, this);
  packedSumOKRealSum[this] := true;
// TODO might need to manipulate fractions for 
// BasicFields inside predicate
    
  return r;
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

//---------------------
//proxysum.bpl

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
requires fracBasicFieldsProxySum[this] > 0.0;
requires (n[this] == n1);
requires ( sum[this] == n1 * (n1+1) / 2 );


procedure UnpackSumOKProxySum(n1:int, this:Ref);
requires packedSumOKProxySum[this];
requires fracSumOKProxySum[this] > 0.0;
requires (n[this] == n1);
ensures (sum[this] == (n1 * (n1+1) / 2));

procedure PackSumGreater0ProxySum(n1:int, s1:real, this:Ref);
requires (packedSumGreater0ProxySum[this] == false);
requires fracBasicFieldsProxySum[this] > 0.0;
requires (sum[this] == s1);
requires (s1 > 0.0);

procedure UnpackSumGreater0ProxySum(n1:int, s1:real, this:Ref);
requires packedSumGreater0ProxySum[this];
requires fracSumGreater0ProxySum[this] > 0.0;
requires (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructProxySum(n1:int, this:Ref)
modifies n, sum, realSum;
ensures n[this] == n1;
ensures sum[this] == 0.0;
ensures realSum[this] == null;
ensures packedBasicFieldsProxySum[this];
ensures fracBasicFieldsProxySum[this] == 1.0;
{
	n[this] := n1;
	sum[this] := 0.0;
	realSum[this] := null;
}

procedure calculateSumProxySum(n1:int, s1:real, this:Ref)  returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum,
      packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedBasicFieldsProxySum,
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

	// transfer 

	call PackSumOKProxySum(n[this], this);
	packedSumOKProxySum[this] := true;
	r := sum[this];
}

procedure addOneToSumProxySum(n1:int, s1:real, this:Ref) returns (r:real)
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
    // transfer 

	} 

  call temp := addOneToSumRealSum(realSum[this]);
  sum[this] := temp;
  // transfer 

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

//------------------------------------
//clientsum.bpl

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
requires sumClient[this] == suCli;
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
requires sumClient[this] == suCli;
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

//transfer 

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

//transfer 


call UnpackBasicFieldsProxySum(realSum[s2], sum[s2], n[s2], s2);
packedBasicFieldsProxySum[s2] := false;
call temp1 := addOneToSumProxySum(s2);

call UnpackClientSumGreater0(s2, client4);
packedClientSumGreater0[client4] := false;

call temp2 := checkSumGreater0(client4);
}


