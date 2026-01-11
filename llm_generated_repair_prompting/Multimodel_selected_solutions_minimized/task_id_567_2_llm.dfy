// Checks if an array is sorted in non-decreasing order.
predicate ArrSorted(a: array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1]
}


method IsSortedArr(a: array<int>) returns (sorted: bool)
  ensures sorted <==> ArrSorted(a)
{
    if a.Length > 0 {
        for k := 1 to a.Length
          invariant forall i :: 0 <= i < k - 1 ==> a[i] <= a[i+1]
        {
            if a[k-1] > a[k] {
                return false;
            }
        }
    }
    return true;
}

// Test cases checked statically.
method IsSortedTest(){
  var a1:= new int[] [1, 1, 2, 4, 6];
  var out1 := IsSortedArr(a1);
  assert out1;

  var a2 := new int[] [1, 2, 4, 3, 6];
  assert a2[2] == 4 && a2[3] == 3;

  var out2 := IsSortedArr(a2);
  assert ! out2;
}