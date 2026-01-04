
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
    requires forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1] // Array is sorted in non-decreasing order
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant 1 <= count <= i 
        invariant forall k :: 0 <= k < i - 1 ==> (a[k] != a[k+1] ==> count > 1)
        invariant forall k :: 0 <= k < i ==> (a[k] == a[k+1] ==> count <= i)
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
