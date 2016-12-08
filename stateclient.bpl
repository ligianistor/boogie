var scon: [Ref]Ref;

var packedStateClientMultiple2:[Ref]bool;
var fracStateClientMultiple2:[Ref]real;

var packedStateClientMultiple3:[Ref]bool;
var fracStateClientMultiple3:[Ref]real;

procedure PackStateClientMultiple2(s:Ref, this:Ref)
requires (packedStateClientMultiple2[this] ==false);
requires (scon[this] == s);
requires (fracStateContextMultiple2[s] > 0.0);

procedure UnpackStateClientMultiple2(s:Ref, this:Ref)
requires packedStateClientMultiple2[this];
ensures (scon[this] == s);
ensures (fracStateContextMultiple2[s] > 0.0);

procedure PackStateClientMultiple3(s:Ref, this:Ref)
requires (packedStateClientMultiple3[this] ==false);
requires (scon[this] == s);
requires (fracStateContextMultiple3[s] > 0.0);

procedure UnpackStateClientMultiple3(s:Ref, this:Ref)
requires packedStateClientMultiple3[this];
ensures (scon[this] == s);
ensures (fracStateContextMultiple3[s] > 0.0);

procedure stateClientCheckMultiplicity3(this:Ref) returns (r:bool)
requires packedStateClientMultiple3[this];
requires (fracStateClientMultiple3[this] >= 1.0);
ensures packedStateClientMultiple3[this];
ensures (fracStateClientMultiple3[this] >= 1.0);
{
call r:= stateContextCheckMultiplicity3(scon[this]);
}
 
procedure stateClientCheckMultiplicity2(this:Ref) returns (r:bool)
requires packedStateClientMultiple2[this];
requires (fracStateClientMultiple2[this] >= 1.0);
ensures packedStateClientMultiple2[this];
ensures (fracStateClientMultiple2[this] >= 1.0);
{
call r:= stateContextCheckMultiplicity2(scon[this]);
}
 
procedure main(this:Ref)
{
var st1:Ref;
call ConstructStateLive(st1);
//add more about constructor
//Statelike st1 = new StateLive();

	StateContext scontext1 = new StateContext(stateContextMultiple3()[], stateLive()[])(st1); 
	StateClient sclient1 = new StateClient(stateClientMultiple3()[])(scontext1);
	StateClient sclient2 = new StateClient(stateClientMultiple3()[])(scontext1);
	scontext1.computeResult(1); 
	sclient1.stateClientCheckMultiplicity3(); 
	scontext1.computeResult(2); 
	sclient2.stateClientCheckMultiplicity3(); 
	scontext1.computeResult(3); 
	sclient1.stateClientCheckMultiplicity3(); 

	Statelike st2 = new StateLive();
	StateContext scontext2 = new StateContext(stateContextMultiple2()[], stateLive()[])(st2); 
	StateClient sclient3 = new StateClient(stateClientMultiple2()[])(scontext2);
	StateClient sclient4 = new StateClient(stateClientMultiple2()[])(scontext2); 
	scontext2.computeResult2(1); 
	sclient3.stateClientCheckMultiplicity2(); 
	scontext2.computeResult2(2); 
	sclient4.stateClientCheckMultiplicity2();  
	scontext2.computeResult2(3); 
	sclient3.stateClientCheckMultiplicity2(); 



}

				

