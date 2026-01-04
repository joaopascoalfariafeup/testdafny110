// Rotates left the elements of a non-empty array by one position.
method RotateLeft(a: array<int>) 
 modifies a
 requires a.Length > 0
 ensures a[..] == old(a[..])[1..] + [old(a[0])]
{
    ghost var oa := a[..];
    var tmp := a[0];
    for i := 0 to a.Length - 1
        invariant oa == old(a[..])
        invariant tmp == oa[0]
        invariant 0 <= i <= a.Length - 1
        invariant forall k :: 0 <= k < i ==> a[k] == oa[k + 1]
        invariant forall k :: i <= k < a.Length ==> a[k] == oa[k]
    {
        a[i] := a[i + 1];
    } 
    a[a.Length - 1] := tmp;
    assert a[..] == oa[1..] + [oa[0]];
}

method testRotateLeft()
{
    // normal array
    var a1 := new int[] [1, 2, 3, 4, 5];
    RotateLeft(a1);
    assert a1[..] == [2, 3, 4, 5, 1];

    // unitary array
    var a2 := new int[] [42];
    RotateLeft(a2);
    assert a2[..] == [42];
}
