/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

ghost predicate InSeq(x: int, s: seq<nat>)
{
    exists k :: 0 <= k < |s| && s[k] == x
}

ghost function RecamanSeq(n: nat): seq<nat>
    ensures |RecamanSeq(n)| == n + 1
{
    if n == 0 then [0]
    else 
        var prev := RecamanSeq(n-1);
        var x := prev[n-1] - n;
        if x > 0 && !InSeq(x, prev) then prev + [x]
        else prev + [prev[n-1] + n]
}

ghost function RecamanVal(n: nat): nat
{
    RecamanSeq(n)[n]
}

lemma RecamanSeqLength(n: nat)
    ensures |RecamanSeq(n)| == n + 1
{
}

lemma RecamanSeqPrefix(n: nat, m: nat)
    requires m <= n
    ensures |RecamanSeq(n)| >= m + 1
    ensures |RecamanSeq(m)| >= m + 1
    ensures forall k :: 0 <= k <= m ==> RecamanSeq(n)[k] == RecamanSeq(m)[k]
{
    RecamanSeqLength(n);
    RecamanSeqLength(m);
    if m == n {
    } else {
        RecamanSeqPrefix(n-1, m);
    }
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
    requires len <= a.Length
    ensures res <==> exists k :: 0 <= k < len && a[k] == x
{
    for i := 0 to len
        invariant forall k :: 0 <= k < i ==> a[k] != x
    {
        if a[i] == x {
            return true;
        }
    }
    return false;
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
    ensures res == RecamanVal(n)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
        invariant forall k :: 0 <= k < i ==> a[k] == RecamanSeq(i-1)[k]
    {
        RecamanSeqLength(i-1);
        RecamanSeqLength(i);
        RecamanSeqPrefix(i, i-1);
        
        ghost var prevSeq := RecamanSeq(i-1);
        ghost var currSeq := RecamanSeq(i);
        
        var x  := a[i-1] - i;
        if x > 0 {
            var c := Contains(x, a, i);
            assert c <==> InSeq(x, prevSeq) by {
                assert forall k :: 0 <= k < i ==> a[k] == prevSeq[k];
            }
            if ! c {
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
    RecamanSeqLength(n);
    return a[n];
}

method {:fuel RecamanSeq, 15} {:fuel RecamanVal, 15} {:fuel InSeq, 15} TestRecaman() {
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
