/* the Recaman's sequence is defined as: 
    R(0) = 0
    For n > 0, R(n) = R(n-1) - n if positive and not already in the sequence, otherwise R(n) = R(n-1) + n.
*/

predicate ContainsPred(x: int, a: array<nat>, len: nat)
  reads a
{
  exists i: nat :: i < len && i < a.Length && a[i] == x
}

// Sequence version for the mathematical specification
predicate ContainsSeqPred(x: int, s: seq<nat>, len: nat)
{
  exists i: nat :: i < len && i < |s| && s[i] == x
}

method Contains(x: int, a: array<nat>, len: nat) returns (res: bool)
  requires a != null
  requires len <= a.Length
  ensures res == ContainsPred(x, a, len)
{
    res := false;
    var i: nat := 0;
    while i < len
      invariant 0 <= i <= len
      invariant forall j: nat :: j < i ==> a[j] != x
      invariant res == false
    {
        if a[i] == x {
            res := true;
            return;
        }
        i := i + 1;
    }
}

// Returns the n-th term of Recaman's sequence
method Recaman(n: nat) returns (res: nat)
  ensures res == RecamanSeq(n)
{
    var a: array<nat> := new nat[n+1];
    a[0] := 0;
    var i: nat := 1;
    while i <= n
      invariant 1 <= i <= n+1
      invariant a.Length == n+1
      invariant forall j: nat :: j < i ==> a[j] == RecamanSeq(j)
      invariant forall j: nat :: j < i ==> ContainsPred(a[j], a, j) == (exists k: nat :: k < j && a[k] == a[j])
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
        i := i + 1;
    }
    res := a[n];
}

function {:fuel 10} RecamanSeq(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else
    var prev := RecamanSeq(n-1);
    var candidate := prev - n;
    if candidate > 0 && !ContainsSeqPred(candidate, RecamanSeqSeq(n-1), n) then
      candidate
    else
      prev + n
}

function {:fuel 10} RecamanSeqSeq(m: nat): seq<nat>
  decreases m
{
  if m == 0 then [0]
  else RecamanSeqSeq(m-1) + [RecamanSeq(m)]
}

lemma RecamanSeqSeqLemma(m: nat)
  ensures RecamanSeqSeq(m) == seq_func(m+1, RecamanSeq)
  decreases m
{
  if m > 0 {
    RecamanSeqSeqLemma(m-1);
  }
}

function seq_func(n: nat, f: nat -> nat): seq<nat>
  decreases n
{
  if n == 0 then []
  else seq_func(n-1, f) + [f(n-1)]
}

lemma ContainsSeqPredLemma(x: nat, m: nat)
  requires m >= 0
  ensures ContainsSeqPred(x, RecamanSeqSeq(m), m+1) == (exists i: nat :: i <= m && RecamanSeq(i) == x)
  decreases m
{
  if m == 0 {
    // base case
    assert RecamanSeqSeq(0) == [0];
    assert ContainsSeqPred(x, [0], 1) == (x == 0);
    assert (exists i: nat :: i <= 0 && RecamanSeq(i) == x) == (x == 0);
  } else {
    ContainsSeqPredLemma(x, m-1);
    var s := RecamanSeqSeq(m);
    assert s == RecamanSeqSeq(m-1) + [RecamanSeq(m)];
    // Prove equivalence
    if RecamanSeq(m) == x {
      assert ContainsSeqPred(x, s, m+1) == true;
      assert (exists i: nat :: i <= m && RecamanSeq(i) == x) == true;
    } else {
      // Show that if x is in s[0..m], it must be in s[0..m-1]
      assert ContainsSeqPred(x, s, m+1) == ContainsSeqPred(x, RecamanSeqSeq(m-1), m);
      assert (exists i: nat :: i <= m && RecamanSeq(i) == x) == (exists i: nat :: i <= m-1 && RecamanSeq(i) == x);
    }
  }
}

method TestRecaman() {
    var r0 := Recaman(0); assert r0 == 0;
    var r1 := Recaman(1); assert r1 == 1;
    var r2 := Recaman(2); assert r2 == 3;  
    var r3 := Recaman(3); assert r3 == 6;
    var r4 := Recaman(4); assert r4 == 2;
    var r5 := Recaman(5); assert r5 == 7;
    var r6 := Recaman(6); 
    // Helper assertions to help verification
    assert r6 == 13 by {
        var seq5 := RecamanSeqSeq(5);
        RecamanSeqSeqLemma(5);
        ContainsSeqPredLemma(1, 5);
        calc {
          RecamanSeq(6);
          ==
          {
            var prev := RecamanSeq(5);
            assert prev == 7;
            var candidate := prev - 6;
            assert candidate == 1;
            assert seq5 == seq_func(6, RecamanSeq);
            assert seq5 == [RecamanSeq(0), RecamanSeq(1), RecamanSeq(2), RecamanSeq(3), RecamanSeq(4), RecamanSeq(5)];
            assert seq5 == [0, 1, 3, 6, 2, 7];
            assert ContainsSeqPred(1, seq5, 6) == true;
          }
          7 + 6;
          ==
          13;
        }
    }
    var r7 := Recaman(7); 
    assert r7 == 20 by {
        var seq6 := RecamanSeqSeq(6);
        RecamanSeqSeqLemma(6);
        ContainsSeqPredLemma(6, 6);
        calc {
          RecamanSeq(7);
          ==
          {
            var prev := RecamanSeq(6);
            assert prev == 13;
            var candidate := prev - 7;
            assert candidate == 6;
            assert seq6 == seq_func(7, RecamanSeq);
            assert seq6 == [0, 1, 3, 6, 2, 7, 13];
            assert ContainsSeqPred(6, seq6, 7) == true;
          }
          13 + 7;
          ==
          20;
        }
    }
    var r8 := Recaman(8); 
    assert r8 == 12 by {
        var seq7 := RecamanSeqSeq(7);
        RecamanSeqSeqLemma(7);
        ContainsSeqPredLemma(12, 7);
        calc {
          RecamanSeq(8);
          ==
          {
            var prev := RecamanSeq(7);
            assert prev == 20;
            var candidate := prev - 8;
            assert candidate == 12;
            assert seq7 == seq_func(8, RecamanSeq);
            assert seq7 == [0, 1, 3, 6, 2, 7, 13, 20];
            assert ContainsSeqPred(12, seq7, 8) == false;
          }
          12;
        }
    }
}




