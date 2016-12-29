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
var i1, i2 : Ref;
var st1 : Ref;
var scontext1 : Ref;
var sclient1, sclient2, sclient3, sclient4 : Ref;

assume (i1!=i2);
assume (sclient1 != sclient2);
assume (sclient3 != sclient4);

call ConstructIntCell(15, i1);
packedMultipleOf15[i1] := false;
call PackMultipleOf15(i1);
packedMultipleOf15[i1] := true;
fracMultipleOf15[i1] := 1.0;

call ConstructStateLive(i1, st1);
packedStateMultipleOf3StateLive[st1] := false;
call PackStateMultipleOf3StateLive(i1, st1);
packedStateMultipleOf3StateLive[st1] := true;
fracStateMultipleOf3StateLive[st1] := 1.0;

instanceof[st1] := 1;

call ConstructStateContext(st1, scontext1);
packedStateContextMultiple3[scontext1] := false;
call PackStateContextMultiple3(st1, scontext1);
packedStateContextMultiple3[scontext1] := true;
fracStateContextMultiple3[scontext1] := 1.0;

call ConstructStateClient(scontext1, sclient1);
packedStateClientMultiple3[sclient1] := false;
call PackStateClientMultiple3(scontext1, sclient1);
packedStateClientMultiple3[sclient1] := true;
fracStateClientMultiple3[sclient1] := 1.0;

call ConstructStateClient(scontext1, sclient2);
packedStateClientMultiple3[sclient2] := false;
call PackStateClientMultiple3(scontext1, sclient2);
packedStateClientMultiple3[sclient2] := true;
fracStateClientMultiple3[sclient2] := 1.0;

call computeResult(1, scontext1);
call stateClientCheckMultiplicity3(sclient1); 
call computeResult(2, scontext1); 
call stateClientCheckMultiplicity3(sclient2); 
call computeResult(3, scontext1); 
call stateClientCheckMultiplicity3(sclient1); 

call ConstructIntCell(14, i2);
packedMultipleOf14[i2] := false;
call PackMultipleOf14(i2);
packedMultipleOf14[i2] := true;
fracMultipleOf14[i2] := 1.0;

call ConstructStateLive(i2, st2);
packedStateMultipleOf2StateLive[st2] := false;
call PackStateMultipleOf2StateLive(i2, st2);
packedStateMultipleOf2StateLive[st2] := true;
fracStateMultipleOf2StateLive[st2] := 1.0;

instanceof[st2] := 1;

call ConstructStateContext(st2, scontext2);
packedStateContextMultiple2[scontext2] := false;
call PackStateContextMultiple2(st2, scontext2);
packedStateContextMultiple2[scontext2] := true;
fracStateContextMultiple2[scontext2] := 1.0;

call ConstructStateClient(scontext2, sclient3);
packedStateClientMultiple2[sclient3] := false;
call PackStateClientMultiple2(scontext2, sclient3);
packedStateClientMultiple2[sclient3] := true;
fracStateClientMultiple2[sclient3] := 1.0;

call ConstructStateClient(scontext2, sclient4);
packedStateClientMultiple2[sclient4] := false;
call PackStateClientMultiple2(scontext2, sclient4);
packedStateClientMultiple2[sclient4] := true;
fracStateClientMultiple2[sclient4] := 1.0;

call computeResult2(1, scontext2);
call stateClientCheckMultiplicity2(sclient3); 
call computeResult2(2, scontext2); 
call stateClientCheckMultiplicity2(sclient4); 
call computeResult2(3, scontext2); 
call stateClientCheckMultiplicity2(sclient3); 			
}

