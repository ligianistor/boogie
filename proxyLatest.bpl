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
requires su>=0.0;

procedure UnpackBasicFieldsRealSum(su:real, n1:int, this:Ref);
requires packedBasicFieldsRealSum[this];
requires fracBasicFieldsRealSum[this] > 0.0;
requires (n[this]==n1);
requires (sum[this] == su);
ensures su>=0.0;
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
ensures n[this] == n1;
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
// since the constructors also have a body now, they ensures forall like the other
// procedures
ensures (forall y:Ref :: ( (y!=this) ==> (n[y] == old(n[y]) ) ) );
ensures (forall y:Ref :: ( (y!=this) ==> (sum[y] == old(sum[y]) ) ) );
ensures (forall y:Ref :: (packedBasicFieldsRealSum[y]));
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
  call temp := calculateSumRealSum(n1, 0.0, this);
}

procedure getRealSum( this:Ref) returns (r:real) 
modifies packedSumOKRealSum, fracBasicFieldsRealSum;
requires packedSumOKRealSum[this];
requires (fracSumOKRealSum[this] > 0.0);
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
ensures (r == sum[this]);
{
	call UnpackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := false;
  	fracBasicFieldsRealSum[this] := 0.1;
	r := sum[this];
	call PackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := true;
}

procedure addOneToSumRealSum(n1:int, s1:real, this:Ref) returns (r:real)
modifies n, sum, packedSumGreater0RealSum, packedSumOKRealSum,
        fracSumOKRealSum, fracSumGreater0RealSum, packedBasicFieldsRealSum, fracBasicFieldsRealSum;
requires packedBasicFieldsRealSum[this];
requires (fracBasicFieldsRealSum[this] > 0.0);
requires (n[this] == n1);
requires (sum[this] == s1);
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
ensures (n[this] == n1);
ensures r > 0.0;
ensures (forall y:Ref :: ( (y!=this) ==> (n[y] == old(n[y]) ) ) );
ensures (forall y:Ref :: (packedBasicFieldsRealSum[y]));
{
  var temp, temp2 : real;
  n[this] := n1;
  call UnpackBasicFieldsRealSum(sum[this], n1, this);
  packedBasicFieldsRealSum[this] := false;
  sum[this] := sum[this] + 1.0;

  call PackBasicFieldsRealSum(sum[this], n1, this);
  packedBasicFieldsRealSum[this] := true;
  packedSumGreater0RealSum[this] := false;
  fracSumGreater0RealSum[this] := fracBasicFieldsRealSum[this];
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
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
ensures r > 0.0;
ensures n[this] == n1;
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
ensures (forall y:Ref :: ( (y!=this) ==> (sum[y] == old(sum[y]) ) ) );
ensures (forall y:Ref :: (packedBasicFieldsRealSum[y]));
{
  call UnpackBasicFieldsRealSum(s1, n1, this);
  packedBasicFieldsRealSum[this] := false;
  sum[this] := n1 * (n1 + 1) / 2;
  r := sum[this];
  call PackBasicFieldsRealSum(n1 * (n1 + 1) / 2, n1, this);
  packedBasicFieldsRealSum[this] := true;
  
  fracSumOKRealSum[this] := fracBasicFieldsRealSum[this];
  packedSumOKRealSum[this] := false; 
  call PackSumOKRealSum(n1, this);
  packedSumOKRealSum[this] := true;    
}


procedure sumIsOKRealSum( this:Ref) returns (r:bool) 
modifies packedSumOKRealSum, fracBasicFieldsRealSum;
requires packedSumOKRealSum[this];
requires (fracSumOKRealSum[this] > 0.0);
ensures packedSumOKRealSum[this];
ensures (fracSumOKRealSum[this] > 0.0);
{
	call UnpackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := false;
	fracBasicFieldsRealSum[this] := 0.1;
	r := (sum[this] == (n[this] * (n[this]+1) / 2));
	call PackSumOKRealSum(n[this], this);
	packedSumOKRealSum[this] := true;
}

procedure sumIsGreater0RealSum(this:Ref)  returns (r:bool)
modifies packedSumGreater0RealSum, fracBasicFieldsRealSum, fracSumGreater0ProxySum;
requires packedSumGreater0RealSum[this];
requires (fracSumGreater0RealSum[this] > 0.0);
ensures packedSumGreater0RealSum[this];
ensures (fracSumGreater0RealSum[this] > 0.0);
{
	call UnpackSumGreater0RealSum(n[this], sum[this], this);
	packedSumGreater0RealSum[this] := false;
	fracBasicFieldsRealSum[this] := 0.1;
	r:= (sum[this] > 0.0);
  
	call PackSumGreater0RealSum(n[this], sum[this], this);
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

procedure PackSumOKProxySum(n1:int, rs:Ref, this:Ref);
requires (packedSumOKProxySum[this] == false);
requires fracBasicFieldsProxySum[this] > 0.0;
requires (n[this] == n1);
requires ( sum[this] == n1 * (n1+1) / 2 );


procedure UnpackSumOKProxySum(n1:int, rs:Ref, this:Ref);
requires packedSumOKProxySum[this];
requires fracSumOKProxySum[this] > 0.0;
requires (n[this] == n1);
ensures (sum[this] == (n1 * (n1+1) / 2));

procedure PackSumGreater0ProxySum(n1:int, s1:real, rs:Ref, this:Ref);
requires (packedSumGreater0ProxySum[this] == false);
requires fracBasicFieldsProxySum[this] > 0.0;
requires (sum[this] == s1);
requires (s1 > 0.0);

procedure UnpackSumGreater0ProxySum(n1:int, s1:real, rs:Ref, this:Ref);
requires packedSumGreater0ProxySum[this];
requires fracSumGreater0ProxySum[this] > 0.0;
requires (sum[this] == s1);
ensures	(s1 > 0.0);

procedure ConstructProxySum(n1:int, this:Ref)
modifies n, sum, realSum;
ensures n[this] == n1;
ensures sum[this] == 0.0;
ensures realSum[this] == null;
{
	n[this] := n1;
	sum[this] := 0.0;
	realSum[this] := null;
}

procedure calculateSumProxySum(n1:int, s1:real, ob:Ref, this:Ref)  returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum,
      packedBasicFieldsRealSum, fracBasicFieldsRealSum, packedBasicFieldsProxySum,
      packedSumOKProxySum, fracSumOKProxySum;
requires packedBasicFieldsProxySum[this];
requires (fracBasicFieldsProxySum[this] > 0.0);
requires n[this] == n1;
requires sum[this] == s1;
requires realSum[this] == ob;
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
requires (ob!=null) ==> ( packedSumOKRealSum[ob] && (fracSumOKRealSum[ob] > 0.0) && (n[ob] == n[this]) );
ensures packedSumOKProxySum[this];
ensures	(fracSumOKProxySum[this] > 0.0);
ensures n[this] == n1;
ensures (forall y:Ref :: (packedBasicFieldsProxySum[y] == old(packedBasicFieldsProxySum[y])));
ensures (forall y:Ref :: (packedBasicFieldsRealSum[y]));
{ 
	var temp : real;

	call UnpackBasicFieldsProxySum(ob, s1, n1, this);
	packedBasicFieldsProxySum[this] := false;

	if (ob==null) {
		call ConstructRealSum(n[this], ob);
		packedSumOKRealSum[ob] := true;
		fracSumOKRealSum[ob] := 1.0;
	}
	call temp := getRealSum(ob);
	sum[this] := temp;

	call PackBasicFieldsProxySum(ob, sum[this], n1, this);
	packedBasicFieldsProxySum[this]:= true;
  
  	call UnpackSumOKRealSum(n[ob], ob);
  	packedSumOKRealSum[ob] := false;
  
  // Just for this case when we have to pack to a bigger predicate
  // that contains a smaller predicate but we don't have the bigger
  // predicate unpacked.
  	packedSumOKProxySum[this] := false;
	call PackSumOKProxySum(n[this], ob, this);
	packedSumOKProxySum[this] := true;
  	fracSumOKProxySum[this] := fracBasicFieldsProxySum[this];
	r := sum[this];
}

procedure addOneToSumProxySum(n1:int, s1:real, ob:Ref, this:Ref) returns (r:real)
modifies n, sum, packedSumOKRealSum, fracSumOKRealSum,
        packedBasicFieldsRealSum, fracBasicFieldsRealSum,
        packedSumGreater0RealSum, fracSumGreater0RealSum,
        packedSumGreater0ProxySum, packedBasicFieldsProxySum,
        fracSumGreater0ProxySum;
requires packedBasicFieldsProxySum[this];
requires (fracBasicFieldsProxySum[this] > 0.0);
requires n[this] == n1;
requires sum[this] == s1;
requires realSum[this] == ob;
requires (ob!=null) ==> ( packedBasicFieldsRealSum[ob] && (fracBasicFieldsRealSum[ob] > 0.0) && (n[ob] == n[this]));
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] > 0.0);
ensures (forall y:Ref :: (packedBasicFieldsProxySum[y] == old(packedBasicFieldsProxySum[y])));
ensures (forall y:Ref :: (packedBasicFieldsRealSum[y]));
{
	var temp : real;
  	call UnpackBasicFieldsProxySum(ob, s1, n1, this);
	packedBasicFieldsProxySum[this] := false;

	if (ob == null) {
		call ConstructRealSum(n[this], ob);
		packedSumOKRealSum[ob] := true;
		fracSumOKRealSum[ob] := 1.0;
    		call UnpackSumOKRealSum(n[ob], ob);
    		packedSumOKRealSum[ob] := false;
    		fracBasicFieldsRealSum[ob] := 0.1;
	} 

	  call temp := addOneToSumRealSum(n[ob], sum[ob], ob);

	  sum[this] := temp;
    
    	  call PackBasicFieldsProxySum(ob, temp, n1, this);
	  packedBasicFieldsProxySum[this] := true;
    
    	  packedSumGreater0ProxySum[this] := false;
	  call PackSumGreater0ProxySum(n1, sum[this], ob, this);
	  packedSumGreater0ProxySum[this] := true;
    	  fracSumGreater0ProxySum[this] := fracBasicFieldsProxySum[this];
	  r := sum[this];
}

procedure sumIsOKProxySum(this:Ref) returns (r:bool)
modifies packedSumOKProxySum, fracBasicFieldsProxySum;
requires packedSumOKProxySum[this];
requires (fracSumOKProxySum[this] > 0.0);
ensures packedSumOKProxySum[this];
ensures (fracSumOKProxySum[this] > 0.0); 
{
	call UnpackSumOKProxySum(n[this], realSum[this], this);
	packedSumOKProxySum[this] := false;
	fracBasicFieldsProxySum[this] := 0.1;
	r := (sum[this] == (n[this] * (n[this]+1) / 2.0));
	call PackSumOKProxySum(n[this], realSum[this], this);
	packedSumOKProxySum[this] := true;
}

procedure sumIsGreater0ProxySum(this:Ref)  returns (r:bool)
modifies packedSumGreater0ProxySum, fracBasicFieldsProxySum;
requires packedSumGreater0ProxySum[this];
requires (fracSumGreater0ProxySum[this] > 0.0);
ensures packedSumGreater0ProxySum[this];
ensures (fracSumGreater0ProxySum[this] > 0.0);
{
	call UnpackSumGreater0ProxySum(n[this], sum[this], realSum[this], this);
	packedSumGreater0ProxySum[this] := false;
	fracBasicFieldsProxySum[this] := 0.1;
	r:= (sum[this] > 0.0);
	call PackSumGreater0ProxySum(n[this], sum[this], realSum[this], this);
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
requires (instanceof[suCli] == 1) ==> (fracSumOKProxySum[suCli] > 0.0) ;
requires (instanceof[suCli] == 2) ==> (fracSumOKRealSum[suCli] > 0.0) ;

procedure UnpackClientSumOK(suCli:Ref, this:Ref);
requires packedClientSumOK[this];
requires fracClientSumOK[this] > 0.0;
requires sumClient[this] == suCli;
ensures (instanceof[suCli] == 1) ==> (fracSumOKProxySum[suCli] > 0.0) ;
ensures (instanceof[suCli] == 2) ==> (fracSumOKRealSum[suCli] > 0.0) ;

procedure PackClientSumGreater0(suCli:Ref, this:Ref);
requires (packedClientSumGreater0[this] == false);
requires sumClient[this] == suCli;
requires (instanceof[suCli] == 1) ==> (fracSumGreater0ProxySum[suCli] > 0.0) ;
requires (instanceof[suCli] == 2) ==> (fracSumGreater0RealSum[suCli] > 0.0) ;

procedure UnpackClientSumGreater0(suCli:Ref, this:Ref);
requires packedClientSumGreater0[this];
requires fracClientSumGreater0[this] > 0.0;
requires sumClient[this] == suCli;
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
modifies packedSumOKRealSum, packedSumOKProxySum, fracBasicFieldsProxySum, fracBasicFieldsRealSum;
requires packedClientSumOK[this];
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
ensures packedClientSumOK[this];
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
modifies packedSumGreater0RealSum, packedSumGreater0ProxySum, fracBasicFieldsProxySum, 
   fracBasicFieldsRealSum, fracSumGreater0ProxySum;
requires packedClientSumGreater0[this];
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
ensures packedClientSumGreater0[this];
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
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));

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

call temp := calculateSumProxySum(n[s], sum[s],realSum[s], s);

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

call temp2 := checkSumIsOK(client1);

call UnpackSumOKProxySum(n[s], realSum[s], s);
packedSumOKProxySum[s] := false;
fracBasicFieldsProxySum[s] := 0.1;

call temp := calculateSumProxySum( n[s],sum[s],realSum[s], s);

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
requires (forall y:Ref :: (packedBasicFieldsRealSum[y]));
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

call temp1 := addOneToSumProxySum(n[s2], sum[s2], realSum[s2], s2);

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

call temp2 := checkSumGreater0(client3);

call UnpackSumGreater0ProxySum( n[s2],sum[s2], realSum[s2], s2);
packedSumGreater0ProxySum[s2] := false;
fracBasicFieldsProxySum[s2] := 0.1;

call temp1 := addOneToSumProxySum(n[s2], sum[s2],realSum[s2],s2);

call temp2 := checkSumGreater0(client4);
}


