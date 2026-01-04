/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

predicate InSeq(x: int, s: seq<nat>)
{
  exists j: nat :: j < |s| && s[j] == x
}

predicate InArrayPrefix(x: int, a: array<nat>, len: nat)
{
  exists j: nat :: j < len && a[j] == x
}

lemma InArrayPrefixEquivInSeq(x: int, a: array<nat>, len: nat)
  requires len <= a.Length
  ensures InArrayPrefix(x, a, len) <==> InSeq(x, a[..len])
{
  if InArrayPrefix(x, a, len) {
    var j: nat :| j < len && a[j] == x;
    assert j < |a[..len]|;
    assert a[..len][j] == a[j];
    assert InSeq(x, a[..len]);
  } else {
    if InSeq(x, a[..len]) {
      var j: nat :| j < |a[..len]| && a[..len][j] == x;
      assert j < len;
      assert a[..len][j] == a[j];
      assert InArrayPrefix(x, a, len);
    }
  }
}

function {:fuel 50} RecSeq(n: nat): seq<nat>
  decreases n
{
  if n == 0 then
    [0]
  else
    var s := RecSeq(n - 1);
    s + [
      if (s[n - 1] - n) > 0 && !InSeq(s[n - 1] - n, s)
      then (s[n - 1] - n) as nat
      else s[n - 1] + n
    ]
}

function {:fuel 50} Rec(n: nat): nat
{
  RecSeq(n)[n]
}


method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires len <= a.Length
  ensures res <==> InArrayPrefix(x, a, len)
{
    for i := 0 to len
      invariant 0 <= i <= len
      invariant forall j: nat :: j < i ==> a[j] != x
    {
        if a[i] == x {
            assert InArrayPrefix(x, a, len);
            return true;
        }
    }
    assert !InArrayPrefix(x, a, len);
    return false;
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
  ensures res == Rec(n)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    for i := 1 to n + 1  
      invariant 1 <= i <= n + 1
      invariant a.Length == n + 1
      invariant a[..i] == RecSeq((i - 1) as nat)
    {
       var x  := a[i-1] - i;
       if x > 0 {
           var c := Contains(x, a, i);
           assert c <==> InArrayPrefix(x, a, i);
           InArrayPrefixEquivInSeq(x, a, i);
           assert c <==> InSeq(x, a[..i]);
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

        assert RecSeq(i as nat) ==
          RecSeq((i - 1) as nat) + [
            if (RecSeq((i - 1) as nat)[(i - 1) as nat] - i) > 0
               && !InSeq(RecSeq((i - 1) as nat)[(i - 1) as nat] - i, RecSeq((i - 1) as nat))
            then (RecSeq((i - 1) as nat)[(i - 1) as nat] - i) as nat
            else RecSeq((i - 1) as nat)[(i - 1) as nat] + i
          ];

        assert a[..(i + 1)] == a[..i] + [a[i]];

        if x > 0 {
          InArrayPrefixEquivInSeq(x, a, i);
          assert InSeq(x, a[..i]) <==> InSeq(x, RecSeq((i - 1) as nat));
          if !InSeq(x, a[..i]) {
            assert a[i] ==
              (if (a[i - 1] - i) > 0 && !InSeq(a[i - 1] - i, a[..i])
               then (a[i - 1] - i) as nat
               else a[i - 1] + i);
          } else {
            assert a[i] ==
              (if (a[i - 1] - i) > 0 && !InSeq(a[i - 1] - i, a[..i])
               then (a[i - 1] - i) as nat
               else a[i - 1] + i);
          }
        } else {
          assert a[i] ==
            (if (a[i - 1] - i) > 0 && !InSeq(a[i - 1] - i, a[..i])
             then (a[i - 1] - i) as nat
             else a[i - 1] + i);
        }

        assert a[..(i + 1)] == RecSeq(i as nat);
    }
    assert a[..(n + 1)] == RecSeq(n);
    assert a[n] == Rec(n);
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
