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
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
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
      // Prove the ordering invariant for the newly added element
      // For any idx1 < idx2 where idx2 is the new index (|res|-1)
      // We need to show there exist k1 < k2 < i+1 with the properties
      // Case 1: idx2 is not the new index - handled by previous invariant
      // Case 2: idx2 is the new index (|res|-1) and idx1 < |res|-1
      // Then we need k1 < i and k2 = i
      // Since res[idx1] is already in res, by invariant there exists k1 < i with a[k1] = res[idx1] and a[k1] !in a[..k1]
      // And we have a[i] = res[|res|-1] and a[i] !in a[..i]
      // Also k1 < i by the existence from invariant
    }
    i := i + 1;
  }
}

// Helper lemma to prove test assertions
lemma TestHelper<T>(a: array<T>, res: seq<T>)
  requires forall i :: 0 <= i < a.Length && a[i] !in a[..i] ==> a[i] in res
  requires forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k]
  requires forall idx1, idx2 :: 0 <= idx1 < idx2 < |res| ==> 
      exists k1, k2 :: 0 <= k1 < k2 < a.Length && a[k1] == res[idx1] && a[k2] == res[idx2] && a[k1] !in a[..k1] && a[k2] !in a[..k2]
  ensures forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k] && (forall j :: 0 <= j < i ==> exists m :: 0 <= m < k && a[m] == res[j] && a[m] !in a[..m])
{
  // This lemma is not strictly needed for verification but we keep it
}

// Helper function to extract first occurrences in order
ghost function FirstOccurrences<T(==)>(a: array<T>) : seq<T>
  ensures |FirstOccurrences(a)| <= a.Length
  ensures forall x :: x in FirstOccurrences(a) ==> x in a[..]
  ensures forall i :: 0 <= i < |FirstOccurrences(a)| ==> exists k :: 0 <= k < a.Length && a[k] == FirstOccurrences(a)[i] && a[k] !in a[..k]
  ensures forall i, j :: 0 <= i < j < |FirstOccurrences(a)| ==> FirstOccurrences(a)[i] != FirstOccurrences(a)[j]
  ensures forall idx1, idx2 :: 0 <= idx1 < idx2 < |FirstOccurrences(a)| ==> 
      exists k1, k2 :: 0 <= k1 < k2 < a.Length && a[k1] == FirstOccurrences(a)[idx1] && a[k2] == FirstOccurrences(a)[idx2] && a[k1] !in a[..k1] && a[k2] !in a[..k2]
  ensures forall i :: 0 <= i < a.Length && a[i] !in a[..i] ==> a[i] in FirstOccurrences(a)
{
  if a.Length == 0 then []
  else if a[a.Length-1] !in a[..a.Length-1] then FirstOccurrences(a[..a.Length-1]) + [a[a.Length-1]]
  else FirstOccurrences(a[..a.Length-1])
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
  
  // Use the postconditions to prove res1 == [1, 2]
  assert |res1| <= 4;
  assert forall x :: x in res1 ==> x in [1, 2, 1, 2];
  assert forall i, j :: 0 <= i < j < |res1| ==> res1[i] != res1[j];
  assert 1 in res1 && 2 in res1;
  
  // Prove exact length using the postconditions
  // All elements that are first occurrences must be in res1
  assert a1[0] !in a1[..0] ==> a1[0] in res1;
  assert a1[1] !in a1[..1] ==> a1[1] in res1;
  
  // From the postcondition: forall i :: 0 <= i < a.Length && a[i] !in a[..i] ==> a[i] in res
  // a1[0] and a1[1] are first occurrences, so both must be in res1
  // From uniqueness postcondition, res1 has distinct elements
  // So |res1| >= 2
  
  // Also from postcondition: forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k]
  // The only elements with a[k] !in a[..k] are a[0]=1 and a[1]=2
  // So res1 can only contain 1 and 2
  // Therefore |res1| == 2
  // Use the helper function to prove this
  var fo1 := FirstOccurrences(a1);
  assert fo1 == [1, 2];
  assert |fo1| == 2;
  // Show that res1 must equal fo1
  assert forall x :: x in res1 ==> x in fo1;
  assert forall x :: x in fo1 ==> x in res1;
  assert |res1| == |fo1|;
  // From ordering preservation, the elements must be in the same order
  assert res1 == fo1;
  assert |res1| == 2;
  
  // Additional assertions to help prove the exact sequence
  // From ordering preservation: for idx1=0, idx2=1, there exist k1 < k2 with a[k1]=res[0], a[k2]=res[1]
  // The only possibilities are k1=0, k2=1 since those are the only first occurrences
  // So res[0] = a[0] = 1 and res[1] = a[1] = 2
  assert res1[0] == 1;
  assert res1[1] == 2;
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  // Add helper assertions
  assert a2[..] == [1, 1, 1];
  assert a2[0] == 1 && a2[1] == 1 && a2[2] == 1;
  assert a2[0] !in a2[..0]; // true
  assert a2[1] in a2[..1]; // true since a2[..1] = [1] contains 1
  assert a2[2] in a2[..2]; // true since a2[..2] = [1,1] contains 1
  
  // Use the postconditions to prove res2 == [1]
  assert |res2| <= 3;
  assert forall x :: x in res2 ==> x in [1, 1, 1];
  assert forall i, j :: 0 <= i < j < |res2| ==> res2[i] != res2[j];
  assert 1 in res2;
  
  // Prove exact length: only a2[0] is a first occurrence
  // So res2 must contain exactly 1
  // From postcondition: forall i :: 0 <= i < |res| ==> exists k :: 0 <= k < a.Length && a[k] == res[i] && a[k] !in a[..k]
  // The only k with a[k] !in a[..k] is k=0
  // So |res2| == 1
  // Use the helper function to prove this
  var fo2 := FirstOccurrences(a2);
  assert fo2 == [1];
  assert |fo2| == 1;
  // Show that res2 must equal fo2
  assert forall x :: x in res2 ==> x in fo2;
  assert forall x :: x in fo2 ==> x in res2;
  assert |res2| == |fo2|;
  assert res2 == fo2;
  assert |res2| == 1;
  assert res2 == [1];
}

