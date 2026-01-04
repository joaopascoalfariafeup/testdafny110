// Checks if an array is sorted in non-decreasing order.
predicate SortedArr(a: array<int>)
  reads a
{
  forall i:int :: 1 <= i < a.Length ==> a[i-1] <= a[i]
}

method IsSortedArr(a: array<int>) returns (sorted: bool)
  ensures sorted == SortedArr(a)
{
    if a.Length > 0 {
        for k := 1 to a.Length
          invariant 1 <= k <= a.Length
          invariant forall i:int :: 1 <= i < k ==> a[i-1] <= a[i]
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
  var out2 := IsSortedArr(a2);
  assert ! out2;
}
