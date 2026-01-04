
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i+1]
  ensures count <= a.Length
  ensures a.Length == 0 ==> count == 0
  ensures a.Length > 0 ==> count >= 1
  ensures count == |set i | 0 <= i < a.Length :: a[i]|
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant count >= 1
      invariant count <= i
      invariant count == 1 + |set k | 1 <= k < i && a[k] != a[k-1] :: k|
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    assert count == 1 + |set k | 1 <= k < a.Length && a[k] != a[k-1] :: k|;
    assert count == |set i | 0 <= i < a.Length :: a[i]|;
    return count;
}



method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}
