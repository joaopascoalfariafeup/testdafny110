
predicate IsInArray(x: int, a: seq<nat>, len: nat)
{
    exists k :: 0 <= k < len && a[k] == x
}

ghost function Contains(x: int, a: seq<nat>, len: nat): bool
  requires x >= 0
  requires len <= |a|
  ensures Contains(x, a, len) <==> IsInArray(x, a, len)
{
    if len == 0 then false
    else if a[len-1] == x then true
    else Contains(x, a, len-1)
}

ghost function RecamanSeq(n: nat): seq<nat>
  requires n >= 0
  ensures |RecamanSeq(n)| == n + 1
  ensures RecamanSeq(n)[0] == 0
  ensures forall k :: 0 < k <= n ==> (RecamanSeq(n)[k] == RecamanSeq(n)[k-1] - k && RecamanSeq(n)[k] > 0 && !IsInArray(RecamanSeq(n)[k], RecamanSeq(n), k)) || RecamanSeq(n)[k] == RecamanSeq(n)[k-1] + k
{
    var a := [0];
    for i in 1 .. n + 1
      invariant i <= n+1
    {
        var x := a[i-1] - i;
        if x > 0 && !Contains(x, a, i) {
            a := a + [x];
        } else {
            a := a + [a[i-1] + i];
        }
    }
    a
}

method Recaman(n: nat) returns (res: nat)
  requires n >= 0
  ensures forall k :: 0 <= k < n ==> !IsInArray(res, old(RecamanSeq(n)), k)
{
    var a: seq<nat> := [0];
    for i in 1 .. n + 1  
      invariant i <= n+1
    {
       var x  := a[i-1] - i;
       if x > 0 {
           var c := Contains(x, a, i);
           if ! c {
             a := a + [x];
           } 
           else {
             a := a + [a[i-1] + i];
           }
       } 
        else {
            a := a + [a[i-1] + i];
        }
    }
    res := a[n];
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


