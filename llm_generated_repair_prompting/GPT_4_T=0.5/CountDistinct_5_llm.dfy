
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // The array is sorted in non-decreasing order
  ensures 0 <= count <= a.Length // The count of distinct elements is always between 0 and the length of the array
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] != a[j] ==> count > 0 // If there are distinct elements, count is more than 0
  ensures count == (if a.Length == 0 then 0 else 1) + sum(if i == 0 then 0 else if a[i] != a[i-1] then 1 else 0 for i in seq(1..a.Length)) // Count is the sum of distinct elements
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

