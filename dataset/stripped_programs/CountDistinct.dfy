
// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
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

    var unsorted := new int[] [3, 1, 3];
    //@invalid var counted2 := CountDistinct(unsorted); // violates pre-condition
}