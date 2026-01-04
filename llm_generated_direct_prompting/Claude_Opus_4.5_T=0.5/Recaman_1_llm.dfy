/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

predicate InArray(x: int, a: array<nat>, len: nat)
    reads a
    requires len <= a.Length
{
    exists k :: 0 <= k < len && a[k] == x
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
    requires len <= a.Length
    ensures res == InArray(x, a, len)
{
    for i := 0 to len
        invariant !InArray(x, a, i)
    {
        if a[i] == x {
            return true;
        }
    }
    return false;
}

ghost function RecamanSeq(n: nat): seq<nat>
    decreases n
{
    if n == 0 then [0]
    else 
        var prev := RecamanSeq(n-1);
        var last := prev[n-1];
        var candidate := last - n;
        if candidate > 0 && candidate !in prev then
            prev + [candidate]
        else
            prev + [last + n]
}

ghost function R(n: nat): nat
{
    RecamanSeq(n)[n]
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
    ensures res == R(n)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
        invariant forall k :: 0 <= k < i ==> a[k] == RecamanSeq(n)[k]
        invariant forall k :: 0 <= k < i ==> a[k] in RecamanSeq(i-1)
    {
       var x  := a[i-1] - i;
       if x > 0 {
           var c := Contains(x, a, i);
           if ! c {
             assert x !in RecamanSeq(i-1);
             a[i] := x;
           } 
           else {
             a[i] := a[i-1] + i;
           }
       } 
        else {
            a[i] := a[i-1] + i;
        }
    }
    return a[n];
}

method {:fuel R,10} {:fuel RecamanSeq,10} TestRecaman() {
    var r0 := Recaman(0); assert r0 == 0;
    var r1 := Recaman(1); assert r1 == 1;
    var r2 := Recaman(2); assert r2 == 3;  
    var r3 := Recaman(3); assert r3 == 6;
    var r4 := Recaman(4); assert r4 == 2;
    var r5 := Recaman(5); assert r5 == 7;
    var r6 := Recaman(6); assert r6 == 13;
    var r7 := Recaman(7); assert r7 == 20;
    var r8 := Recaman(8); assert r8 == 12; // decreases
}
