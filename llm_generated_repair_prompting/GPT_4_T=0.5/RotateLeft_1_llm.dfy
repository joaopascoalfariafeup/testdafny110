// Rotates left the elements of a non-empty array by one position.
method RotateLeft(a: array<int>) 
  requires a.Length > 0
  modifies a
  ensures forall k :: 0 <= k < a.Length - 1 ==> a[k] == old(a[k + 1])
  ensures a[a.Length - 1] == old(a[0])
{
    var tmp := a[0];
    for i := 0 to a.Length - 1
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] == old(a[k + 1])
      invariant i < a.Length ==> tmp == old(a[0])
    {
        a[i] := a[i + 1];
    } 
    a[a.Length - 1] := tmp;
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
