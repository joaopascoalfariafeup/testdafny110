
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
    requires forall k :: 1 <= k < a.Length ==> a[k-1] <= a[k] // The input array is sorted in non-decreasing order
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant 1 <= count <= i // The count is always between 1 and the current index (inclusive)
        invariant forall k :: 1 <= k < i ==> a[k] != a[k-1] ==> count >= 2 // If there are distinct elements in the array, count is at least 2
        invariant forall k, j :: 0 <= k < j < i && a[k] != a[j] ==> count > 1 // If there are distinct elements in the array, count is more than 1
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
