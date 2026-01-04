
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures count <= a.Length
  ensures a.Length == 0 ==> count == 0
  ensures a.Length > 0 ==> 1 <= count <= a.Length
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      invariant count <= a.Length
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
