// Checks if an array is sorted in non-decreasing order.
method IsSortedArr(a: array<int>) returns (sorted: bool)
  ensures sorted <==> (forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1])
{
    if a.Length > 1 {
        for k := 1 to a.Length - 1
          invariant 1 <= k <= a.Length - 1
          // We have established the ordering for all adjacent pairs strictly before k
          invariant forall i :: 0 <= i < k-1 ==> a[i] <= a[i+1]
        {
            if a[k-1] > a[k] {
                // returning false implies there exists a violating adjacent pair
                assert exists i :: 0 <= i < a.Length - 1 && a[i] > a[i+1];
                return false;
            }
            // establish the pair (k-1, k) so the invariant holds for the next iteration
            assert forall i :: 0 <= i < k ==> a[i] <= a[i+1];
        }
        // At loop exit, we only know the invariant with k == a.Length - 1, i.e.
        // forall i :: 0 <= i < a.Length - 2 ==> a[i] <= a[i+1]
        // The last pair (a.Length-2, a.Length-1) was checked in the final iteration,
        // but it is not retained by the loop invariant, so we cannot assert it here.
        assert forall i :: 0 <= i < a.Length - 2 ==> a[i] <= a[i+1];
    }
    return true;
}

// Test cases checked statically.
method IsSortedTest(){
  var a1:= new int[] [1, 1, 2, 4, 6];
  assert a1[..] == [1, 1, 2, 4, 6];
  var out1 := IsSortedArr(a1);
  assert out1;

  var a2 := new int[] [1, 2, 4, 3, 6];
  assert a2[..] == [1, 2, 4, 3, 6];
  var out2 := IsSortedArr(a2);
  // help Dafny see a concrete adjacent inversion (index 2: 4 > 3)
  assert 0 <= 2 < a2.Length - 1 && a2[2] > a2[3];
  assert ! out2;
}
