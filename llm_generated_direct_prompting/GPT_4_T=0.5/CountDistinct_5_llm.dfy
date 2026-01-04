
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // a is sorted in non-decreasing order
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
        invariant 1 <= count <= i // count is always between 1 and i
        invariant forall k :: 0 <= k < i ==> a[k] != a[i] ==> count > 1 // if a distinct element is found, count is more than 1
        invariant forall k, l :: 0 <= k < l < i && a[k] != a[l] ==> count > 1 // if distinct elements are found in the traversed part of the array, count is more than 1
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
    ensures count >= 1 && count <= a.Length // count is always between 1 and the length of the array
    ensures forall i, j :: 0 <= i < j < a.Length && a[i] != a[j] ==> count > 1 // if distinct elements are found in the array, count is more than 1
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
