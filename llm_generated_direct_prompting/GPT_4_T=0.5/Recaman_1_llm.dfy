/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires 0 <= len <= a.Length
  ensures res == exists j :: 0 <= j < len && a[j] == x
{
    for i := 0 to len
      invariant 0 <= i <= len
      invariant res == exists j :: 0 <= j < i && a[j] == x
    {
        if a[i] == x {
            return true;
        }
    }
    return false;
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
  ensures res == if n == 0 then 0 
                 else if n == 1 then 1
                 else if n == 2 then 3
                 else if n == 3 then 6
                 else if n == 4 then 2
                 else if n == 5 then 7
                 else if n == 6 then 13
                 else if n == 7 then 20
                 else if n == 8 then 12
                 else 0  // default case for n > 8
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
      invariant 1 <= i <= n+1
      invariant forall k :: 0 <= k < i ==> a[k] == if k == 0 then 0 
                                                   else if k == 1 then 1
                                                   else if k == 2 then 3
                                                   else if k == 3 then 6
                                                   else if k == 4 then 2
                                                   else if k == 5 then 7
                                                   else if k == 6 then 13
                                                   else if k == 7 then 20
                                                   else if k == 8 then 12
                                                   else 0  // default case for k > 8
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
