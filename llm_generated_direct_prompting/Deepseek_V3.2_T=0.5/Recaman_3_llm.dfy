/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

predicate ContainsPred(x: int, a: array<nat>, len: nat)
  reads a
{
  exists k :: 0 <= k < len && a[k] == x
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires a != null
  requires len <= a.Length
  ensures res == ContainsPred(x, a, len)
{
    for i := 0 to len
      invariant forall k :: 0 <= k < i ==> a[k] != x
      invariant res == false
    {
        if a[i] == x {
            res := true;
            return;
        }
    }
    res := false;
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
  ensures res == RecamanSeq(n)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
      invariant a != null
      invariant a.Length == n+1
      invariant forall j :: 0 <= j < i ==> a[j] == RecamanSeq(j)
      invariant forall j :: 0 <= j < i ==> a[j] >= 0
    {
       var x  := a[i-1] - i;
       if x > 0 {
           var c := Contains(x, a, i);
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
    res := a[n];
}

function RecamanSeq(n: nat): nat
{
  if n == 0 then 0
  else
    var prev := RecamanSeq(n-1);
    var candidate := prev - n;
    if candidate > 0 && !ExistsInRecamanSeq(candidate, n-1) then candidate
    else prev + n
}

predicate ExistsInRecamanSeq(x: int, m: nat)
{
  exists k :: 0 <= k <= m && RecamanSeq(k) == x
}

method TestRecaman() {
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
