// Given a non-empty array 'a' of natural numbers, generates a new array 'b' 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.

ghost function Count(s: seq<nat>, k: nat): nat
{
   if |s| == 0 then 0
   else (if s[|s|-1] == k then 1 else 0) + Count(s[..|s|-1], k)
}

ghost function Max(s: seq<nat>): nat
   requires |s| > 0
{
   if |s| == 1 then s[0]
   else if s[|s|-1] > Max(s[..|s|-1]) then s[|s|-1] else Max(s[..|s|-1])
}

ghost predicate ValidBuckets(b: seq<nat>, a: seq<nat>, m: nat)
{
   |b| == m + 1 &&
   (forall k :: 0 <= k <= m ==> b[k] == Count(a, k))
}

lemma MaxProperty(s: seq<nat>, i: int)
   requires |s| > 0
   requires 0 <= i < |s|
   ensures s[i] <= Max(s)
{
   if |s| == 1 {
   } else if i == |s| - 1 {
   } else {
      MaxProperty(s[..|s|-1], i);
   }
}

lemma CountBound(s: seq<nat>, k: nat)
   ensures Count(s, k) <= |s|
{
   if |s| == 0 {
   } else {
      CountBound(s[..|s|-1], k);
   }
}

method MakeBuckets(a: array<nat>) returns(b: array<nat>)
   requires a.Length > 0
   ensures b.Length == Max(a[..]) + 1
   ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..], k)
{
   var max := a[0];
   for i := 1 to a.Length
      invariant max == Max(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }
      assert a[..i+1][..i] == a[..i];
   }
   assert a[..a.Length] == a[..];

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   for i := 0 to a.Length
      invariant b.Length == max + 1
      invariant forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i], k)
   {
      ghost var oldCount := b[a[i]];
      b[a[i]] := b[a[i]] + 1;
      assert a[..i+1][..i] == a[..i];
      assert a[..i+1][|a[..i+1]|-1] == a[i];
      forall k | 0 <= k < b.Length
         ensures b[k] == Count(a[..i+1], k)
      {
         assert Count(a[..i+1], k) == (if a[i] == k then 1 else 0) + Count(a[..i], k);
      }
   }
   assert a[..a.Length] == a[..];
}



// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);
    assert a1[..] == [1, 2, 2, 3];
    assert Max(a1[..]) == 3;
    assert Count(a1[..], 0) == 0;
    assert Count(a1[..], 1) == 1;
    assert Count(a1[..], 2) == 2;
    assert Count(a1[..], 3) == 1;
    assert b1[..] == [0, 1, 2, 1]; 
    
    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);
    assert a2[..] == [0];
    assert Max(a2[..]) == 0;
    assert Count(a2[..], 0) == 1;
    assert b2[..] == [1];
}

