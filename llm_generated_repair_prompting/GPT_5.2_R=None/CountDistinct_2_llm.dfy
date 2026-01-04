
// Helper predicate to avoid brittle quantifier triggers in loop invariants
ghost predicate IsChangeAt(a: array<int>, j: int)
  requires a != null
{
  1 <= j < a.Length && a[j] != a[j-1]
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires a != null
  requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
  ensures count <= a.Length
  ensures a.Length == 0 ==> count == 0
  ensures a.Length > 0 ==> count >= 1
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      // Each change position j contributes one of the counted "new distincts"
      invariant forall j {:trigger IsChangeAt(a,j)} ::
                 1 <= j < i && a[j] != a[j-1] ==>
                 exists k :: 2 <= k <= count && a[j] == a[k-1]
      // Each counted "new distinct" corresponds to some change position j
      invariant forall k {:trigger a[k-1]} ::
                 2 <= k <= count ==>
                 exists j :: 1 <= j < i && a[j] != a[j-1] && a[j] == a[k-1]
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

