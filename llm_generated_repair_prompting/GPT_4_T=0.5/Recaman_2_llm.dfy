
predicate IsInArray(x: int, a: array<nat>, len: nat)
{
    exists k :: 0 <= k < len && a[k] == x
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires x >= 0
  requires len <= a.Length
  ensures res <==> IsInArray(x, a, len)
{
    for i := 0 to len
      invariant forall k :: 0 <= k < i ==> a[k] != x
      invariant i <= len
    {
        if a[i] == x {
            return true;
        }
    }
    return false;
}

ghost method RecamanArray(n: nat) returns (a: array<nat>)
  ensures |a| == n + 1
  ensures a[0] == 0
  ensures forall k :: 0 < k <= n ==> (a[k] == a[k-1] - k && a[k] > 0 && !IsInArray(a[k], a, k)) || a[k] == a[k-1] + k
{
    a := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1
      invariant i <= n+1
    {
        var x := a[i-1] - i;
        if x > 0 && !Contains(x, a, i) {
            a[i] := x;
        } else {
            a[i] := a[i-1] + i;
        }
    }
}

method Recaman(n: nat) returns (res: nat)
  ensures forall k :: 0 <= k < n ==> !IsInArray(res, old(RecamanArray(n).a), k)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
      invariant i <= n+1
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

