module IntersectionModule {

  // Returns a sequence with elements that belong to both sequences, without duplicates.
  // The result follows the ordering of elements in the first sequence.
  // In case the first sequence has duplicates, it keeps an arbitrary occurrence.
  function {:fuel 5} SeqIntersection(axs: seq<int>, bs: seq<int>): seq<int>
    decreases |axs|
    ensures forall k :: 0 <= k < |SeqIntersection(axs, bs)| ==>
              SeqIntersection(axs, bs)[k] in axs && SeqIntersection(axs, bs)[k] in bs
    ensures forall i, j :: 0 <= i < j < |SeqIntersection(axs, bs)| ==>
              SeqIntersection(axs, bs)[i] != SeqIntersection(axs, bs)[j]
  {
    if |axs| == 0 then []
    else
      (let r := SeqIntersection(axs[..|axs|-1], bs) in
        if axs[|axs|-1] in bs && axs[|axs|-1] !in r then r + [axs[|axs|-1]] else r)
  }

  // One-step unfolding helper for the iterative proof
  lemma SeqIntersectionStep(axs: seq<int>, bs: seq<int>, x: int)
    ensures SeqIntersection(axs + [x], bs) ==
              (if x in bs && x !in SeqIntersection(axs, bs) then SeqIntersection(axs, bs) + [x] else SeqIntersection(axs, bs))
  {
    assert |axs + [x]| == |axs| + 1;
    assert |axs + [x]| > 0;
    assert (axs + [x])[..|(axs + [x])|-1] == axs;
    assert (axs + [x])[|(axs + [x])|-1] == x;

    calc {
      SeqIntersection(axs + [x], bs);
      ==
      (let r := SeqIntersection((axs + [x])[..|(axs + [x])|-1], bs) in
        if (axs + [x])[|(axs + [x])|-1] in bs && (axs + [x])[|(axs + [x])|-1] !in r
        then r + [(axs + [x])[|(axs + [x])|-1]]
        else r);
      ==
      (let r := SeqIntersection(axs, bs) in
        if x in bs && x !in r then r + [x] else r);
      ==
      (if x in bs && x !in SeqIntersection(axs, bs) then SeqIntersection(axs, bs) + [x] else SeqIntersection(axs, bs));
    }
  }

  method Intersection(a: array<int>, b: array<int>) returns (res: seq<int>)
    requires a != null && b != null
    ensures res == SeqIntersection(a[..], b[..])
    ensures forall k :: 0 <= k < |res| ==> res[k] in a[..] && res[k] in b[..]
    ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  {
    res := [];
    for i := 0 to a.Length - 1
      invariant 0 <= i <= a.Length
      invariant res == SeqIntersection(a[..i], b[..])
    {
      // Help the verifier connect the loop step with the recursive definition
      SeqIntersectionStep(a[..i], b[..], a[i]);

      if a[i] in b[..] && a[i] !in res {
        // From the invariant, rewrite the membership test against SeqIntersection
        assert res == SeqIntersection(a[..i], b[..]);
        assert a[i] !in SeqIntersection(a[..i], b[..]);

        res := res + [a[i]];

        // Use the step lemma to justify the new res
        assert res == SeqIntersection(a[..i], b[..]) + [a[i]];
        assert res == SeqIntersection(a[..i] + [a[i]], b[..]);
      } else {
        assert res == SeqIntersection(a[..i], b[..]);
      }

      assert a[..i] + [a[i]] == a[..i+1];

      // Connect the iteration to SeqIntersection on the extended prefix
      calc {
        res;
        ==
        (if a[i] in b[..] && a[i] !in SeqIntersection(a[..i], b[..])
           then SeqIntersection(a[..i], b[..]) + [a[i]]
           else SeqIntersection(a[..i], b[..]));
        ==
        SeqIntersection(a[..i] + [a[i]], b[..]);
        ==
        SeqIntersection(a[..i+1], b[..]);
      }
    }

    // From the loop invariant at i == a.Length
    assert res == SeqIntersection(a[..a.Length], b[..]);
    assert a[..a.Length] == a[..];
    assert res == SeqIntersection(a[..], b[..]);
  }

  // Test cases checked statically
  method IntersectionTest() {
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
}
