
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count == 1 + |{ k: int | 1 <= k < i && a[k] != a[k-1] }|
    {
        if i < a.Length && a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}





