
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires IsSorted(a)
  ensures count == |AsSet(a)|
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    assert AsSet(a, 1) == {a[0]}; // helper
    for i := 1 to a.Length
      invariant count == |AsSet(a, i)|
    {
        if a[i] != a[i-1] {
            count := count + 1;
            assert AsSet(a, i+1) == AsSet(a, i) + {a[i]}; //helper
        }
        else {
            assert AsSet(a, i+1) == AsSet(a, i); //helper
        }
    }
    return count;
}

// Checks if array 'a' is sorted.
ghost predicate IsSorted(a: array<int>) 
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Obtains the content of array 'a' as a set.
ghost function AsSet(a: array<int>, n: nat := a.Length): set<int> 
  reads a
{
    set k | 0 <= k < n <= a.Length :: a[k] 
}

method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert a[0] == a[1] < a[2] == a[3] < a[4]; // helper
    assert AsSet(a, 5) == {1, 2, 3}; // helper
    assert count == 3;
    
    var unsorted := new int[] [3, 1, 3];
    //@invalid var counted2 := CountDistinct(unsorted); // violates pre-condition
}