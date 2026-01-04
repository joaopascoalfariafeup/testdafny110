/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

predicate ContainsPredicate(x: int, a: array<nat>, len: nat)
  reads a
{
  exists k: nat :: k < len && a[k] == x
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires a != null
  requires len <= a.Length
  ensures res == ContainsPredicate(x, a, len)
{
    for i := 0 to len
      invariant 0 <= i <= len
      invariant forall k: nat :: k < i ==> a[k] != x
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
      invariant 1 <= i <= n+1
      invariant a != null && a.Length == n+1
      invariant forall k: nat :: k < i ==> a[k] == RecamanSeq(k)
      invariant forall k: nat :: k < i ==> ContainsPredicate(a[k], a, i)
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
  decreases n
{
  if n == 0 then 0
  else
    var prev := RecamanSeq(n-1);
    var candidate := prev - n;
    if candidate > 0 && !ContainsPredicate(candidate, RecamanArray(n-1), n) then
      candidate
    else
      prev + n
}

function RecamanArray(n: nat): array<nat>
  decreases n
  ensures result != null
  ensures result.Length == n+1
  ensures forall k: nat :: k <= n ==> result[k] == RecamanSeq(k)
{
  if n == 0 then
    var a := new nat[1];
    a[0] := 0;
    a
  else
    var aPrev := RecamanArray(n-1);
    var a := new nat[n+1];
    var i: nat := 0;
    while i < n
      invariant 0 <= i <= n
      invariant a != null && a.Length == n+1
      invariant forall k: nat :: k < i ==> a[k] == aPrev[k]
    {
      a[i] := aPrev[i];
      i := i + 1;
    }
    var prev := aPrev[n-1];
    var candidate := prev - n;
    if candidate > 0 && !ContainsPredicate(candidate, aPrev, n) then
      a[n] := candidate
    else
      a[n] := prev + n;
    a
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
