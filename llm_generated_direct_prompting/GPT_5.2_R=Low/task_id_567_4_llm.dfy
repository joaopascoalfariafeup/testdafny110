// Checks if an array is sorted in non-decreasing order.
predicate SortedSeq(s: seq<int>)
{
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

method IsSortedArr(a: array<int>) returns (sorted: bool)
  ensures sorted <==> SortedSeq(a[..])
{
    if a.Length > 0 {
        for k := 1 to a.Length
          invariant 1 <= k <= a.Length
          invariant forall i :: 0 <= i < k - 1 ==> a[i] <= a[i + 1]
        {
            if a[k-1] > a[k] {
                assert 0 <= k - 1 < a.Length - 1;
                assert !SortedSeq(a[..]);
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
