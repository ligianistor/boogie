var myState: [Ref]Ref;

var packedBasicFieldsContext : [Ref]bool;
var fracBasicFieldsContext : [Ref]real;

var packedStateContextMultiple2 : [Ref]bool;
var fracStateContextMultiple2 : [Ref]real;

var packedStateContextMultiple3 : [Ref]bool;
var fracStateContextMultiple3 : [Ref]real;

procedure PackStateContextMultiple2(m:Ref, this:Ref);
requires (packedStateContextMultiple2[this] == false);
requires (myState[this] == m);
requires (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] >= 1.0);
requires (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] >= 1.0);
requires (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] >= 1.0);

procedure UnpackStateContextMultiple2(m:Ref, this:Ref);
requires packedStateContextMultiple2[this];
ensures (myState[this] == m);
ensures (instanceof[m] == 1) ==> (fracStateMultipleOf2StateLive[this] >= 1.0);
ensures (instanceof[m] == 2) ==> (fracStateMultipleOf2StateLimbo[this] >= 1.0);
ensures (instanceof[m] == 3) ==> (fracStateMultipleOf2StateSleep[this] >= 1.0);

//	predicate BasicFieldsContext() = exists m:StateLike :: this.myState -> m

//	predicate stateLive() = myState instanceof StateLive
//	predicate stateSleep() = myState instanceof StateSleep
//	predicate stateLimbo() = myState instanceof StateLimbo
//	predicate stateContextMultiple2() = myState#1 StateMultipleOf2() 
//	predicate stateContextMultiple3() = myState#1 StateMultipleOf3() 
	
StateContext() 
ensures this#1 stateLive() 
{ 
	setState(new StateLive()); 
} 

void setState(Statelike newState) { 
	myState = newState; 
} 

procedure computeResultSC(num: int) returns (r:Ref)
modifies 
ensures packedStateContextMultiple3[this];
ensures fracStateContextMultiple3[this] >= 1.0;
ensures (old(instanceof[mystate[this]]) == 1) ==> (instanceof[mystate[this]] == 2);
ensures (old(instanceof[mystate[this]]) == 2) ==> (instanceof[mystate[this]] == 3);
ensures (old(instanceof[mystate[this]]) == 3) ==> (instanceof[mystate[this]] == 1);
{
var temp : Ref;
if (instanceof[myState[this]]) == 1) {
	call temp := computeResultStateLive(this, num, myState[this]);
} else if (instanceof[mystate[this]]) == 2) {
	call temp := computeResultStateLimbo(this, num, myState[this]);
} else {
	call temp := computeResultStateSleep(this, num, myState[this]);
}

}


