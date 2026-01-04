// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.

function {:fuel 10} Count(s: seq<nat>, v: nat): nat
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

function {:fuel 10} MaxSeq(s: seq<nat>): nat
  requires |s| > 0
  decreases |s|
  ensures MaxSeq(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
{
  if |s| == 1 then s[0]
  else
    var m := MaxSeq(s[..|s|-1]);
    if s[|s|-1] <= m then m else s[|s|-1]
}

lemma MaxSeqExtend(s: seq<nat>, x: nat)
  requires |s| > 0
  ensures MaxSeq(s + [x]) == (if x <= MaxSeq(s) then MaxSeq(s) else x)
{
  // By unfolding MaxSeq on the last element
  calc {
    MaxSeq(s + [x]);
    == { }
    (if |s + [x]| == 1 then (s + [x])[0]
     else
       (var m := MaxSeq((s + [x])[..|s + [x]|-1]);
        if (s + [x])[|s + [x]|-1] <= m then m else (s + [x])[|s + [x]|-1]));
    == { assert |s + [x]| == |s| + 1; }
    (var m := MaxSeq((s + [x])[..|s|]);
     if (s + [x])[|s|] <= m then m else (s + [x])[|s|]);
    == { assert (s + [x])[..|s|] == s; assert (s + [x])[|s|] == x; }
    (var m := MaxSeq(s); if x <= m then m else x);
    == { }
    (if x <= MaxSeq(s) then MaxSeq(s) else x);
  }
}

lemma CountNil(v: nat)
  ensures Count([], v) == 0
{
}

lemma CountExtend(s: seq<nat>, v: nat, x: nat)
  ensures Count(s + [x], v) == Count(s, v) + (if x == v then 1 else 0)
{
  // Expand Count on the last element
  calc {
    Count(s + [x], v);
    == { }
    Count((s + [x])[..|(s + [x])| - 1], v) + (if (s + [x])[|(s + [x])| - 1] == v then 1 else 0);
    == { assert |s + [x]| == |s| + 1; }
    Count((s + [x])[..|s|], v) + (if (s + [x])[|s|] == v then 1 else 0);
    == { assert (s + [x])[..|s|] == s; assert (s + [x])[|s|] == x; }
    Count(s, v) + (if x == v then 1 else 0);
  }
}

lemma SeqExt<T>(s1: seq<T>, s2: seq<T>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures s1 == s2
{
}

method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + MaxSeq(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..], k)
  ensures forall i :: 0 <= i < a.Length ==> a[i] < b.Length
{
   var max := a[0];

   // Establish the loop invariant at i == 1
   assert a[..1] == [a[0]];
   assert MaxSeq(a[..1]) == a[0];

   for i := 1 to a.Length
     invariant 1 <= i <= a.Length
     invariant max == MaxSeq(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }

      // Re-establish max == MaxSeq(a[..i+1])
      assert a[..i+1] == a[..i] + [a[i]];
      assert MaxSeq(a[..i+1]) == MaxSeq(a[..i] + [a[i]]);
      assert MaxSeq(a[..i] + [a[i]]) == (if a[i] <= MaxSeq(a[..i]) then MaxSeq(a[..i]) else a[i]) by {
        MaxSeqExtend(a[..i], a[i]);
      }
      assert max == MaxSeq(a[..i+1]);
   }

   // Conclude max is the maximum of a[..]
   assert max == MaxSeq(a[..a.Length]);
   assert a[..] == a[..a.Length];
   assert MaxSeq(a[..]) == max;

   b := new nat[1 + max];

   // Initialize all buckets to 0
   forall k | 0 <= k <= max {
     b[k] := 0;
   }

   // Help the verifier connect the initializer range (<= max) with (< b.Length)
   assert b.Length == 1 + max;
   assert forall k :: 0 <= k < b.Length ==> b[k] == 0;

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall j :: 0 <= j < a.Length ==> a[j] <= max
     invariant forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i], k)
   {
      ghost var bs := b[..];
      // snapshot matches the current invariant
      assert forall k :: 0 <= k < b.Length ==> bs[k] == Count(a[..i], k);

      b[a[i]] := b[a[i]] + 1;

      assert forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i+1], k)
      by {
        forall k | 0 <= k < b.Length
          ensures b[k] == Count(a[..i+1], k)
        {
          assert a[..i+1] == a[..i] + [a[i]];
          assert Count(a[..i+1], k) == Count(a[..i] + [a[i]], k);
          assert Count(a[..i] + [a[i]], k) == Count(a[..i], k) + (if a[i] == k then 1 else 0) by {
            CountExtend(a[..i], k, a[i]);
          }

          if k == a[i] {
            assert b[k] == bs[k] + 1;
            assert bs[k] == Count(a[..i], k);
          } else {
            assert b[k] == bs[k];
            assert bs[k] == Count(a[..i], k);
          }
        }
      }
   }

   // Bridge a[..a.Length] to a[..]
   assert a[..] == a[..a.Length];
}



// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    assert a1[..] == [1, 2, 2, 3];
    assert MaxSeq(a1[..]) == 3;
    var b1 := MakeBuckets(a1);
    assert b1.Length == 4;

    // Use the postcondition b1[k] == Count(a1[..], k) and compute concrete counts
    assert Count(a1[..], 0) == 0;
    assert Count(a1[..], 1) == 1;
    assert Count(a1[..], 2) == 2;
    assert Count(a1[..], 3) == 1;

    assert b1[0] == Count(a1[..], 0);
    assert b1[1] == Count(a1[..], 1);
    assert b1[2] == Count(a1[..], 2);
    assert b1[3] == Count(a1[..], 3);
    assert b1[0] == 0 && b1[1] == 1 && b1[2] == 2 && b1[3] == 1;

    // Prove the whole sequence equality by extensionality
    assert |b1[..]| == 4;
    SeqExt(b1[..], [0, 1, 2, 1]);
    assert b1[..] == [0, 1, 2, 1];

    var a2 := new nat[] [0];
    assert a2[..] == [0];
    assert MaxSeq(a2[..]) == 0;
    var b2 := MakeBuckets(a2);
    assert b2.Length == 1;

    assert Count(a2[..], 0) == 1;
    assert b2[0] == Count(a2[..], 0);
    assert b2[0] == 1;

    assert |b2[..]| == 1;
    SeqExt(b2[..], [1]);
    assert b2[..] == [1];
}
