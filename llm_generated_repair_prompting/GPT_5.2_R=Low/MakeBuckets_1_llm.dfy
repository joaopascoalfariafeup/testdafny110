// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
function Count(s: seq<nat>, v: nat): nat
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

lemma CountExtend(s: seq<nat>, v: nat, x: nat)
  ensures Count(s + [x], v) == Count(s, v) + (if x == v then 1 else 0)
{
}

method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length > 0
  ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..], k)
  ensures forall i :: 0 <= i < a.Length ==> a[i] < b.Length
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

   b := new nat[1 + max];
   forall k | 0 <= k <= max {
     b[k] := 0;
   }
   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i], k)
   {
      ghost var bs := b[..];
      b[a[i]] := b[a[i]] + 1; 

      assert forall k :: 0 <= k < b.Length ==>
        b[k] == Count(a[..i+1], k)
      by {
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



// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);
    assert b1[..] == [0, 1, 2, 1]; 
    
    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);
    assert b2[..] == [1];
}

