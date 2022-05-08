// Given an array of natural numbers, it returns the sorted array (using
// bubblesort). [3,4,1,9,2,4] → [1,2,3,4,4,9]

predicate Sorted(xs: seq<nat>) {
    forall i, j :: 0 <= i <= j < |xs| ==> xs[i] <= xs[j]
}

method BubbleSort(xs: array<nat>)
    modifies xs
    ensures Sorted(xs[..])
    ensures multiset(xs[..]) == multiset(old(xs[..]))
{
    var n := xs.Length;
    while n > 0
        decreases n
        invariant n >= 0
        invariant Sorted(xs[n..])
        invariant multiset(xs[..]) == multiset(old(xs[..]))
        invariant forall i, j :: 0 <= i < n <= j < xs.Length ==> xs[i] <= xs[j]
    {
        var n2, m := 0, 0;
        while m < n - 1
            invariant n2 <= m <= n - 1
            invariant Sorted(xs[n2..m + 1]) && Sorted(xs[n..])
            invariant multiset(xs[..]) == multiset(old(xs[..]))
            invariant forall i, j :: 0 <= i < n2 <= j <= m ==> xs[i] <= xs[j]
            invariant forall i, j :: 0 <= i < n <= j < xs.Length ==> xs[i] <= xs[j]
        {
            if xs[m] > xs[m + 1] {
                xs[m], xs[m + 1] := xs[m + 1], xs[m];
                n2 := m + 1;
            }
            m := m + 1;
        }
        assert xs[n2..] == xs[n2..n] + xs[n..];
        n := n2;
    }
}