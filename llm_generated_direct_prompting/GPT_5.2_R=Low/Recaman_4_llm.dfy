/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

function RecamanSeq(n: nat): seq<nat>
{
  if n == 0 then
    [0]
  else
    var s := RecamanSeq(n - 1);
    var prev := s[n - 1];
    var cand: int := prev - n;
    if cand > 0 && !((cand as nat) in s) then
      s + [cand as nat]
    else
      s + [prev + n]
}

function RecamanVal(n: nat): nat
{
  RecamanSeq(n)[n]
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires len <= a.Length
  ensures res <==> (exists j: int :: 0 <= j < len && a[j] == x)
{
    for i := 0 to len
      invariant forall j: int :: 0 <= j < i ==> a[j] != x
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
      invariant 1 <= i <= n + 1
      invariant a.Length == n + 1
      invariant a[0] == 0
      invariant a[..i] == RecamanSeq((i - 1) as nat)
    {
       var x  := a[i-1] - i;
       if x > 0 {
           var c := Contains(x, a, i);
           if ! c {
             a[i] := x;
             assert a[..i] == RecamanSeq((i - 1) as nat);
             assert a[..(i+1)] == RecamanSeq(i as nat);
           } 
           else {
             a[i] := a[i-1] + i;
             assert a[..i] == RecamanSeq((i - 1) as nat);
             assert a[..(i+1)] == RecamanSeq(i as nat);
           }
       } 
        else {
            a[i] := a[i-1] + i;
            assert a[..i] == RecamanSeq((i - 1) as nat);
            assert a[..(i+1)] == RecamanSeq(i as nat);
        }
    }
    assert a[..(n+1)] == RecamanSeq(n);
    return a[n];
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
