
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // array is sorted in non-decreasing order
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant 1 <= count <= i // count is always between 1 and i
        invariant forall k :: 0 <= k < i && a[k] != a[k+1] ==> count >= 2 // count is at least 2 if there are distinct elements
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
