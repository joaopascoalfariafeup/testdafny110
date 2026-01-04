// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures |res| <= a.Length
  ensures forall x :: x in res ==> x in a[..]
  ensures forall i :: 0 <= i < a.Length ==> a[i] in res || (exists j :: 0 <= j < i && a[j] == a[i])
  ensures forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]
  // Additional postcondition to ensure ordering is preserved
  ensures forall i :: 0 <= i < a.Length && a[i] !in a[..i] ==> a[i] in res
  ensures forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k]
  // Ordering preservation: the first occurrence of each element appears in the same order as in the array
  ensures forall idx1, idx2 :: 0 <= idx1 < idx2 < |res| ==> 
      exists k1, k2 :: 0 <= k1 < k2 < a.Length && a[k1] == res[idx1] && a[k2] == res[idx2] && a[k1] !in a[..k1] && a[k2] !in a[..k2]
{
  res := [];
  for i := 0 to a.Length
    invariant |res| <= i
    invariant forall x :: x in res ==> x in a[..i]
    invariant forall k :: 0 <= k < i ==> a[k] in res || (exists j :: 0 <= j < k && a[j] == a[k])
    invariant forall m, n :: 0 <= m < n < |res| ==> res[m] != res[n]
    // Additional invariants to preserve ordering
    invariant forall k :: 0 <= k < i && a[k] !in a[..k] ==> a[k] in res
    invariant forall idx :: 0 <= idx < |res| ==> exists k :: 0 <= k < i && a[k] == res[idx] && a[k] !in a[..k]
    invariant forall idx1, idx2 :: 0 <= idx1 < idx2 < |res| ==> 
      exists k1, k2 :: 0 <= k1 < k2 < i && a[k1] == res[idx1] && a[k2] == res[idx2] && a[k1] !in a[..k1] && a[k2] !in a[..k2]
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}

// Helper lemma to prove test assertions
lemma TestHelper<T(==)>(a: array<T>, res: seq<T>)
  requires forall i :: 0 <= i < a.Length && a[i] !in a[..i] ==> a[i] in res
  requires forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k]
  requires forall idx1, idx2 :: 0 <= idx1 < idx2 < |res| ==> 
      exists k1, k2 :: 0 <= k1 < k2 < a.Length && a[k1] == res[idx1] && a[k2] == res[idx2] && a[k1] !in a[..k1] && a[k2] !in a[..k2]
  ensures forall i :: 0 <= i < |res| ==> res[i] == a[i] where a[i] !in a[..i]
{
}

// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  // Add helper assertions
  assert a1[..] == [1, 2, 1, 2];
  assert a1[0] == 1 && a1[1] == 2 && a1[2] == 1 && a1[3] == 2;
  assert a1[0] !in a1[..0]; // true since a1[..0] is empty
  assert a1[1] !in a1[..1]; // true since a1[..1] = [1] and 2 != 1
  assert a1[2] in a1[..2]; // true since a1[..2] = [1,2] contains 1
  assert a1[3] in a1[..3]; // true since a1[..3] = [1,2,1] contains 2
  // Prove ordering: the first occurrences are a[0]=1 and a[1]=2 in order
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  // Add helper assertions
  assert a2[..] == [1, 1, 1];
  assert a2[0] == 1 && a2[1] == 1 && a2[2] == 1;
  assert a2[0] !in a2[..0]; // true
  assert a2[1] in a2[..1]; // true since a2[..1] = [1] contains 1
  assert a2[2] in a2[..2]; // true since a2[..2] = [1,1] contains 1
  assert res2 == [1];
}


