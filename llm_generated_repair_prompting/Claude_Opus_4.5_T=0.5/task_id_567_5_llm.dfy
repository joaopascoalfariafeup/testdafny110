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
  // Show that the sorted condition is false using the concrete witness
  assert a2[2] > a2[3] && 0 <= 2 < 3 < a2.Length;
  assert !(a2[2] <= a2[3]);
  // This directly contradicts the universal quantifier
  assert !IsSorted(a2[..]);
  var out2 := IsSortedArr(a2);
  assert ! out2;
}
