// Returns a sequence with elements that belong to both sequences, without duplicates.
// The result follows the ordering of elements in the first sequence.
// In case the first sequence has duplicates, it keeps an arbitrary occurrence.

function {:fuel 50} SeqIntersection(as: seq<int>, bs: seq<int>): seq<int>
  ensures forall k :: 0 <= k < |SeqIntersection(as, bs)| ==> SeqIntersection(as, bs)[k] in as && SeqIntersection(as, bs)[k] in bs
  ensures forall i, j :: 0 <= i < j < |SeqIntersection(as, bs)| ==> SeqIntersection(as, bs)[i] != SeqIntersection(as, bs)[j]
{
  if |as| == 0 then []
  else
    var r := SeqIntersection(as[..|as|-1], bs);
    if as[|as|-1] in bs && as[|as|-1] !in r then r + [as[|as|-1]] else r
}

// One-step unfolding helper for the iterative proof
lemma SeqIntersectionStep(as: seq<int>, bs: seq<int>, x: int)
  ensures SeqIntersection(as + [x], bs) ==
            (if x in bs && x !in SeqIntersection(as, bs) then SeqIntersection(as, bs) + [x] else SeqIntersection(as, bs))
{
  // Unfold SeqIntersection(as + [x], bs)
  assert |as + [x]| > 0;
  assert (as + [x])[..|(as + [x])|-1] == as;
  assert (as + [x])[|(as + [x])|-1] == x;
}

method Intersection(a: array<int>, b: array<int>) returns (res: seq<int>)
  ensures res == SeqIntersection(a[..], b[..])
  ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] in b[..]
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
{
  res := [];
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == SeqIntersection(a[..i], b[..])
  {
    // Help the verifier connect the loop step with the recursive definition
    SeqIntersectionStep(a[..i], b[..], a[i]);

    if a[i] in b[..] && a[i] !in res { // could expand with nested loops
      res := res + [a[i]];
      assert res == SeqIntersection(a[..i] + [a[i]], b[..]);
    }
    assert a[..i] + [a[i]] == a[..i+1];
    assert res == SeqIntersection(a[..i+1], b[..]);
  }
  assert a[..a.Length] == a[..];
}

// Test cases checked statically
method IntersectionTest(){
  var a := new int[] [1, 2, 3];
  var b := new int[] [1, 3, 1];
  var c := new int[] [2, 4, 6];

  // Typical case
  var res1 := Intersection(a, b);
  assert res1 == [1, 3];

  // Empty intersection
  var res2 := Intersection(b, c);
  assert res2 == [];

  // With duplicates
  var res3 := Intersection(b, a);
  assert res3 == [1, 3] || res3 == [3, 1];
}
