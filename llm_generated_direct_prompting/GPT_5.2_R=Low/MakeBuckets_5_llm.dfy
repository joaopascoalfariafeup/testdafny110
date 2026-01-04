ghost function MaxSeq(s: seq<nat>): nat
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    (if s[|s|-1] > MaxSeq(s[..|s|-1]) then s[|s|-1] else MaxSeq(s[..|s|-1]))
}

ghost function CountPrefix(s: seq<nat>, n: nat, v: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0
  else CountPrefix(s, n-1, v) + (if s[n-1] == v then 1 else 0)
}

lemma MaxSeqUpperBound(s: seq<nat>, m: nat)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] <= m
  ensures MaxSeq(s) <= m
  decreases |s|
{
  if |s| == 1 {
  } else {
    MaxSeqUpperBound(s[..|s|-1], m);
    assert MaxSeq(s[..|s|-1]) <= m;
    assert s[|s|-1] <= m;
  }
}

lemma MaxSeqInSeq(s: seq<nat>)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == MaxSeq(s)
  decreases |s|
{
  if |s| == 1 {
  } else {
    MaxSeqInSeq(s[..|s|-1]);
    if s[|s|-1] > MaxSeq(s[..|s|-1]) {
      assert s[|s|-1] == MaxSeq(s);
    } else {
      assert MaxSeq(s) == MaxSeq(s[..|s|-1]);
    }
  }
}

lemma MaxSeqCharacterization(s: seq<nat>, m: nat)
  requires |s| > 0
  requires (exists i :: 0 <= i < |s| && s[i] == m)
  requires forall i :: 0 <= i < |s| ==> s[i] <= m
  ensures MaxSeq(s) == m
{
  MaxSeqUpperBound(s, m);
  MaxSeqInSeq(s);
  var j :| 0 <= j < |s| && s[j] == MaxSeq(s);
  assert s[j] <= m;
  assert MaxSeq(s) <= m;
  var i :| 0 <= i < |s| && s[i] == m;
  assert s[i] <= MaxSeq(s);
  assert m <= MaxSeq(s);
}


// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + MaxSeq(a[..])
  ensures forall k: nat :: k < b.Length ==> b[k] == CountPrefix(a[..], a.Length as nat, k)
{
   var max := a[0];
   for i := 1 to a.Length
     invariant 1 <= i <= a.Length
     invariant forall j :: 0 <= j < i ==> a[j] <= max
     invariant exists j :: 0 <= j < i && a[j] == max
   {
      if a[i] > max {
         max := a[i];
      }
   } 
   assert forall j :: 0 <= j < a.Length ==> a[j] <= max;
   assert exists j :: 0 <= j < a.Length && a[j] == max;
   MaxSeqCharacterization(a[..], max);
   assert MaxSeq(a[..]) == max;

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   assert forall k: nat :: k < b.Length ==> b[k] == 0;

   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall j :: 0 <= j < a.Length ==> a[j] < b.Length
     invariant forall k: nat :: k < b.Length ==> b[k] == CountPrefix(a[..], i as nat, k)
   {
      b[a[i]] := b[a[i]] + 1; 
      assert forall k: nat :: k < b.Length ==> b[k] == CountPrefix(a[..], (i+1) as nat, k);
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

