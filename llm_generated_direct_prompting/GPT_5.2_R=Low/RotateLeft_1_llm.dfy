// Rotates left the elements of a non-empty array by one position.
function RotLeft(s: seq<int>): seq<int>
  requires |s| > 0
{
  s[1..] + [s[0]]
}

method RotateLeft(a: array<int>) 
  requires a.Length > 0
  modifies a
  ensures a[..] == RotLeft(old(a[..]))
{
    var tmp := a[0];
    for i := 0 to a.Length - 1
      invariant 0 <= i <= a.Length - 1
      invariant tmp == old(a[0])
      invariant forall k :: 0 <= k < i ==> a[k] == old(a[k + 1])
      invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
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
