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
  ensures MaxSeq(s) in s
  ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
{
  if |s| == 1 then s[0]
  else
    var m := MaxSeq(s[..|s|-1]);
    if s[|s|-1] <= m then m else s[|s|-1]
}





method MakeBuckets(a: array<nat>) returns(b: array<nat>)
  requires a.Length > 0
  ensures b.Length == 1 + MaxSeq(a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..], k)
{
   var max := a[0];

   assert a[..1] == [a[0]];
   assert MaxSeq(a[..1]) == a[0];

   for i := 1 to a.Length
     invariant max == MaxSeq(a[..i])
   {
      if a[i] > max {
         max := a[i];
      }

      assert MaxSeq(a[..i+1]) == MaxSeq(a[..i] + [a[i]]);
      assert MaxSeq(a[..i] + [a[i]]) == (if a[i] <= MaxSeq(a[..i]) then MaxSeq(a[..i]) else a[i]);
   }


   b := new nat[1 + max];

   forall k | 0 <= k <= max {
     b[k] := 0;
   }


   for i := 0 to a.Length
     invariant 0 <= i <= a.Length
     invariant b.Length == 1 + max
     invariant forall j :: 0 <= j < a.Length ==> a[j] <= max
     invariant forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i], k)
   {

      b[a[i]] := b[a[i]] + 1;

      assert forall k :: 0 <= k < b.Length ==> b[k] == Count(a[..i+1], k)
      by {
        forall k | 0 <= k < b.Length
          ensures b[k] == Count(a[..i+1], k)
        {
          assert a[..i+1] == a[..i] + [a[i]];

        }
      }
   }

   assert a[..] == a[..a.Length];
}



// A simple test case (checked statically)
method TestMakeBuckets() {
    var a1 := new nat[] [1, 2, 2, 3];
    assert a1[..] == [1, 2, 2, 3];
    var b1 := MakeBuckets(a1);



    assert b1[..] == [0, 1, 2, 1];

    var a2 := new nat[] [0];
    var b2 := MakeBuckets(a2);


    assert b2[..] == [1];
}