
// Checks if an array is sorted in non-decreasing order.
method IsSortedArr(a: array<int>) returns (sorted: bool)
    ensures sorted <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
    if a.Length > 0 {
        for k := 1 to a.Length
            invariant forall i, j :: 0 <= i < j < k ==> a[i] <= a[j]
        {
            if a[k-1] > a[k] {
                return false;
            }
        }
    }
    return true;
}

// Helper predicate to check if array is sorted
ghost predicate IsSorted(a: seq<int>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Helper lemma to show array is not sorted when we have a counterexample
lemma NotSortedWitness(a: array<int>, i: int, j: int)
    requires 0 <= i < j < a.Length
    requires a[i] > a[j]
    ensures !(forall p, q :: 0 <= p < q < a.Length ==> a[p] <= a[q])
{
    // The witness i, j directly contradicts the forall
}

// Lemma that connects the negation to the result
lemma NotSortedImpliesFalse(a: array<int>, sorted: bool)
    requires sorted <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    requires !(forall p, q :: 0 <= p < q < a.Length ==> a[p] <= a[q])
    ensures !sorted
{
    // Direct from the biconditional
}

// Test cases checked statically.
method IsSortedTest(){
  var a1:= new int[] [1, 1, 2, 4, 6];
  assert a1[..] == [1, 1, 2, 4, 6];
  var out1 := IsSortedArr(a1);
  assert out1;

  var a2 := new int[] [1, 2, 4, 3, 6];
  assert a2[..] == [1, 2, 4, 3, 6];
  assert a2[2] == 4 && a2[3] == 3;
  assert a2[2] > a2[3];
  // Use the lemma to establish the array is not sorted
  NotSortedWitness(a2, 2, 3);
  // Assert that the forall is false (this follows from the lemma)
  assert !(forall p, q :: 0 <= p < q < a2.Length ==> a2[p] <= a2[q]);
  var out2 := IsSortedArr(a2);
  // Use the connection lemma
  NotSortedImpliesFalse(a2, out2);
  assert ! out2;
}



