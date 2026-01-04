// Checks if an array is sorted in non-decreasing order.
method IsSortedArr(a: array<int>) returns (sorted: bool)
  ensures sorted == forall k :: 0 <= k < a.Length-1 ==> a[k] <= a[k+1]
{
    if a.Length > 0 {
        for k := 1 to a.Length
          invariant forall j :: 0 <= j < k-1 ==> a[j] <= a[j+1]
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
