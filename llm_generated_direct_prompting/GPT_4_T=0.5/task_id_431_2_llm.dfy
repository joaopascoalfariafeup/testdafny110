// Checks if two arrays have a common element.
method HasCommonElement<T(==)>(a: array<T>, b: array<T>) returns (result: bool)
  requires a.Length > 0 && b.Length > 0
{
    result := false;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> (forall l :: 0 <= l < b.Length ==> a[k] != b[l])
      decreases a.Length - i
    {
        for j := 0 to b.Length
          invariant 0 <= j <= b.Length
          invariant forall k :: 0 <= k < j ==> a[i] != b[k]
          decreases b.Length - j
        {
            if a[i] == b[j] {
                return true;
            }
        }
    }
    return false;
}

// Test cases checked statically
method HasCommonElementTest(){
    // single common element
    var a1 := new int[] [1, 2, 3, 4, 5];
    var a2 := new int[] [5, 6, 7, 8, 9];
    var out1 := HasCommonElement(a1, a2);
    assert out1;

    // no common element
    var a3 := new int[] [1, 2, 3, 4, 5];
    var a4 := new int[] [6, 7, 8, 9];
    var out2 := HasCommonElement(a3, a4);
    assert !out2;

    // multiple common elements
    var a5 := new int[] [1, 0, 1, 0];
    var a6 := new int[] [2, 0, 1];
    var out3 := HasCommonElement(a5,a6);
    assert out3;
}
