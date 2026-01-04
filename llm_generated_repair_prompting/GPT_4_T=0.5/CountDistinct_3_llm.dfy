
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires a != null // The array must not be null
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // The array is sorted in non-decreasing order
  ensures 0 <= count <= a.Length // The count of distinct elements is always between 0 and the length of the array
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] != a[j] ==> count > 0 // If there are distinct elements, count is more than 0
  ensures count == count - 1 + (if a.Length > 1 && a[a.Length - 1] != a[a.Length - 2] then 1 else 0) // The count is incremented if the last element is distinct from the second last
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= count <= i + 1 // Count is always between 1 and i+1
      invariant forall k :: 0 <= k < i ==> (a[k] != a[k+1] ==> count > 1) // If there is a distinct element, count is more than 1
      invariant forall k1, k2 :: 0 <= k1 < k2 < i && a[k1] != a[k2] ==> count > 1 // If there are distinct elements, count is more than 1
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

