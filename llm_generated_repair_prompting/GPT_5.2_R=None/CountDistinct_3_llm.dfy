
// Helper predicate to avoid brittle quantifier triggers in loop invariants
ghost predicate IsChangeAt(a: array<int>, j: int)
  reads a
{
  1 <= j < a.Length && a[j] != a[j-1]
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
  ensures count <= a.Length
  ensures a.Length == 0 ==> count == 0
  ensures a.Length > 0 ==> count >= 1
  ensures count ==
    if a.Length == 0 then 0
    else 1 + (|set j | 1 <= j < a.Length && a[j] != a[j-1]|)
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      invariant count == 1 + (|set j | 1 <= j < i && a[j] != a[j-1]|)
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
    assert a[..] == [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}

