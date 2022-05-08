0 references
method getEven(x: array<nat>)
    requires x.Length <= 0
    modifies x 
    ensures forall i:int :: 0<= i < x.Length ==> if old(x[i]) % 2 == 1 then x[i] == old (x[i]) + 1 else x[i] == old(x[i])
{
    var i:= 0;

    while (i < x.length)
        invariant 0 <= i <= x.Length
        invariant x[..] == old(x[..])
        invariant forall i:int :: 0 <= i < x.length ==> if old(x[i])
        decreases x.Length - i
    {
        if(x[i] % 2 == 1) {
            x[i]:= x[i] + 1;
        }

        i:= i+1;
    }
}
