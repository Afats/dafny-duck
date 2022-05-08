// Given an array of characters, it returns the index of the first ‘e’. [‘c’,’h’,’e’,’e’,’s’,’e’] -> 2

method indexe(x:array<char>) returns (b:int)
//requires x.Length > 0
ensures b >= 0 ==>  0 <= b < x.Length && x[b] == 'e'
ensures b >= 0 ==> forall i :: 0 <= i < b ==> x[i] != 'e'
ensures b < 0 ==> forall i :: 0 <= i < x.Length ==> x[i] != 'e'

ensures -1 <= b < x.Length
ensures 
if 'e' in x[..] then
    0 <= b < x.Length && x[b] == 'e' && forall i :: 0<=i<b ==> x[i] != 'e' // ordering matters
    else
    b == -1 
{
    b:=-1;
    var i:= 0;
    while(i < x.Length)
    invariant 0<=i<=x.Length
    invariant forall j :: 0 <= j < i ==> x[j] != 'e'
    {      
        if(x[i] == 'e'){
            b:= i;
            return b;
            //break;
        }

        i:= i + 1;
    }
    return -1;
}


method Main()
{
    var a:= new char [6]['c','h','e','e','s','e'];
    var j:= indexe(a);
    assert j == 2;
    print j;

}