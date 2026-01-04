predicate HasCommonSeq<T(==)>(sa: seq<T>, sb: seq<T>)
{
  exists i, j :: 0 <= i < |sa| && 0 <= j < |sb| && sa[i] == sb[j]
}

// Checks if two arrays have a common element.
method HasCommonElement<T(==)>(a: array<T>, b: array<T>) returns (result: bool)
  ensures result == HasCommonSeq(a[..], b[..])
{
    result := false;
    for i := 0 to a.Length
      invariant !result
      invariant forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < b.Length ==> a[ii] != b[jj]
    {
        for j := 0 to b.Length
          invariant !result
          invariant forall jj :: 0 <= jj < j ==> a[i] != b[jj]
          invariant forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < b.Length ==> a[ii] != b[jj]
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
    assert a1[..] == [1, 2, 3, 4, 5];
    assert a2[..] == [5, 6, 7, 8, 9];
    assert a1[4] == 5;
    assert a2[0] == 5;
    assert HasCommonSeq(a1[..], a2[..]) by {
      assert 0 <= 4 < |a1[..]|;
      assert 0 <= 0 < |a2[..]|;
      assert a1[..][4] == a1[4];
      assert a2[..][0] == a2[0];
      assert a1[..][4] == a2[..][0];
    }
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
    assert a5[..] == [1, 0, 1, 0];
    assert a6[..] == [2, 0, 1];
    assert a5[1] == 0;
    assert a6[1] == 0;
    assert HasCommonSeq(a5[..], a6[..]) by {
      assert 0 <= 1 < |a5[..]|;
      assert 0 <= 1 < |a6[..]|;
      assert a5[..][1] == a5[1];
      assert a6[..][1] == a6[1];
      assert a5[..][1] == a6[..][1];
    }
    var out3 := HasCommonElement(a5,a6);
    assert out3;
}
