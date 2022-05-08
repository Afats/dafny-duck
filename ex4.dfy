// program verifies
predicate sortedarray(c: array<char>, m:nat, n:nat)
reads c
requires 0 <= m <= n <= c.Length
{
    forall i, j :: m <= i < j < n ==> (c[i] as int) <= (c[j] as int)
}

method ShuffleSort(a: array<char>) returns (b: array<char>)
requires a.Length > 1
ensures sortedarray(b, 0, b.Length)
ensures multiset(b[..]) == multiset(a[..])
{
    b := new char[a.Length];
    var index:int := 0;

    //creating a new b array w/ a values
    while (index < b.Length)
    invariant 0 <= index <= b.Length
    invariant b.Length == a.Length
    invariant b[..index] == a[..index]
    invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var temp:char := a[index];
        b[index] := temp;
        index := index + 1;
    }
    var next:int := 1;

    //sort cycle
    while(next < b.Length)
    invariant 1 <= next <= b.Length
    invariant multiset(b[..next]) == multiset(a[..next])
    invariant sortedarray(b, 0, next)
    {
        var prev:int := next - 1;
        var copiedEle:char := a[next];
        b[next] := b[prev];

        while(prev >= 0 && (copiedEle as int) < (b[prev] as int))
        invariant forall i :: prev < i < next ==> (b[i] as int) > (copiedEle as int)
        invariant -1<=prev<=next-1
        invariant sortedarray(b, 0, next+1)
        //ignore the duplicate var in b and the copiedEle variable in a
        invariant multiset(a[..next+1]) - multiset{copiedEle} == multiset(b[..next+1]) - multiset{b[prev+1]} 
        {   
            // move prev to the right 
            b[prev + 1] := b[prev];
            prev := prev - 1;
        }

        // insert the copiedEle in the right order
        b[prev + 1] := copiedEle;
        next := next + 1;
    }

    //pointing dafny in the right direction for the multiset assert, make sure arrays are intact
    assert a[..a.Length] == a[..];
    assert b[..b.Length] == b[..];

}
