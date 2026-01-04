ghost function NatMax(x: nat, y: nat): nat {
  if x >= y then x else y
}

ghost function {:fuel 3} MaxSeq(s: seq<nat>): nat
  requires |s| > 0
{
  if |s| == 1 then s[0] else NatMax(MaxSeq(s[..|s|-1]), s[|s|-1])
}

ghost function {:fuel 3} Count(s: seq<nat>, k: nat): nat {
  if |s| == 0 then 0
  else Count(s[..|s|-1], k) + (if s[|s|-1] == k then 1 else 0)
}

lemma MaxSeqUpperBound(s: seq<nat>)
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    MaxSeqUpperBound(s[..|s|-1]);
    assert forall i :: 0 <= i < |s|-1 ==> s[i] <= MaxSeq(s[..|s|-1]);
    assert MaxSeq(s) == NatMax(MaxSeq(s[..|s|-1]), s[|s|-1]);
    assert forall i :: 0 <= i < |s|-1 ==> s[i] <= MaxSeq(s);
  }
}

lemma CountExtend(s: seq<nat>, x: nat, k: nat)
  ensures Count(s + [x], k) == Count(s, k) + (if x == k then 1 else 0)
{
}

lemma CountZeroPrefix(i: nat, k: nat)
  ensures Count([][..i], k) == 0
{
}

// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + MaxSeq(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 1 <= i <= a.Length
     invariant max == MaxSeq(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }
   } 

   MaxSeqUpperBound(a[..]);
   assert forall j :: 0 <= j < a.Length ==> a[j] <= max;

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall k :: 0 <= k <= max ==> b[k] == Count(a[..i], k)
     invariant forall j :: 0 <= j < a.Length ==> a[j] <= max
   {
      var v := a[i];
      assert 0 <= v <= max;
      assert forall k :: 0 <= k <= max && k != v ==> b[k] == Count(a[..i], k);
      assert b[v] == Count(a[..i], v);

      b[v] := b[v] + 1;

      assert forall k :: 0 <= k <= max ==> Count(a[..i+1], k) == Count(a[..i], k) + (if v == k then 1 else 0);
      assert forall k :: 0 <= k <= max ==> b[k] == Count(a[..i+1], k);
   } 
}



// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);
    assert b1[..] == [0, 1, 2, 1]; 
    
    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);
    assert b2[..] == [1];
}

