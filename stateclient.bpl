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

}

				

