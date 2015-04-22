var x:[int]int;
procedure test()
modifies x;
requires (exists i:int :: x[i] ==3);
{
x[i] := 2; 
}
