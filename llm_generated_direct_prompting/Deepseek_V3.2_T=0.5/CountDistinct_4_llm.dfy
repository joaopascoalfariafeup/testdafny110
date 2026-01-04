
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
      invariant count == 1 + (|| (seq(1, i) [k | a[k] != a[k-1] && 1 <= k < i]) ||)
      invariant forall k :: 0 <= k < i ==> a[k] == a[i-1] || exists l :: 0 <= l < k && a[l] == a[k]
    {
        if a[i] != a[i-1] {
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
