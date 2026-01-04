// Ghost function specifying the exact (order-preserving) result:
// keep the first occurrence of each element.
ghost function {:fuel 10} RemoveDuplicatesSpec<T>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else
    var t := RemoveDuplicatesSpec(s[..|s|-1]);
    if s[|s|-1] in s[..|s|-1] then t
    else t + [s[|s|-1]]
}

// A small helper lemma to unfold the spec on a one-element extension.
lemma RemoveDuplicatesSpecStep<T>(s: seq<T>, x: T)
  ensures RemoveDuplicatesSpec(s + [x]) ==
            (if x in s then RemoveDuplicatesSpec(s) else RemoveDuplicatesSpec(s) + [x])
{
  // By definition, RemoveDuplicatesSpec looks at the last element.
  // Also, (s + [x])[..|s|] == s
  assert |s + [x]| == |s| + 1;
  assert (s + [x])[|s + [x]| - 1] == x;
  assert (s + [x])[..|s + [x]| - 1] == s;
}

// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == RemoveDuplicatesSpec(a[..])
  ensures forall i :: 0 <= i < |res| ==> res[i] in a[..a.Length]
  ensures forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
  ensures forall i :: 0 <= i < a.Length ==> a[i] in res
  ensures forall x :: x in a[..a.Length] ==> x in res
{
  res := [];
  // Use an index range that is always well-formed (even when a.Length == 0).
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == RemoveDuplicatesSpec(a[..i])
    invariant forall k :: 0 <= k < |res| ==> res[k] in a[..i]
    invariant forall p,q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant forall j :: 0 <= j < i ==> a[j] in res
    invariant forall x :: x in a[..i] ==> x in res
  {
    if i < a.Length {
      // help the verifier connect slice extension
      assert a[..i+1] == a[..i] + [a[i]];
      RemoveDuplicatesSpecStep(a[..i], a[i]);

      if a[i] !in a[..i] {
        res := res + [a[i]];
        assert RemoveDuplicatesSpec(a[..i+1]) == RemoveDuplicatesSpec(a[..i]) + [a[i]];
        assert res == RemoveDuplicatesSpec(a[..i+1]);
      } else {
        assert RemoveDuplicatesSpec(a[..i+1]) == RemoveDuplicatesSpec(a[..i]);
        assert res == RemoveDuplicatesSpec(a[..i+1]);
      }
    }
  }

  // At loop exit, i == a.Length, so res == RemoveDuplicatesSpec(a[..a.Length]) == RemoveDuplicatesSpec(a[..])
  assert a[..a.Length] == a[..];
}



// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert a1[..] == [1, 2, 1, 2];
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert a2[..] == [1, 1, 1];
  assert res2 == [1];
}

