// Finds the maximum distance between equal elements in a non-empty array.
method MaxDistEqual<T(==)>(a: array<T>) returns (maxDist: nat)
  requires a.Length > 0
  ensures maxDist < a.Length
  ensures forall i, j :: 0 <= i <= j < a.Length && a[i] == a[j] ==> j - i <= maxDist
  ensures exists i, j :: 0 <= i <= j < a.Length && a[i] == a[j] && j - i == maxDist
{
  maxDist := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant maxDist < a.Length
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] ==> jj - ii <= maxDist
    invariant exists ii, jj :: (0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] && jj - ii == maxDist) || maxDist == 0
  {
    var j := a.Length - 1;
    while j > i + maxDist
      invariant i <= j < a.Length
      invariant forall k :: j < k < a.Length ==> a[k] != a[i]
      invariant maxDist < a.Length
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] ==> jj - ii <= maxDist
      invariant exists ii, jj :: (0 <= ii < i && 0 <= jj < a.Length && a[ii] == a[jj] && jj - ii == maxDist) || maxDist == 0
    {
      if (a[j] == a[i]) {
        maxDist := j - i;
        break;
      }
      j := j - 1;    
    }
  }
}

method testMaxDistEqual()
{
    var a1 := new int[] [1, 2, 1, 2, 2];
    var d1 := MaxDistEqual(a1);
    // Provide helper assertions to prove the test outcome
    assert a1[..] == [1, 2, 1, 2, 2];
    // The maximum distance is between a[1]=2 and a[4]=2, distance 3
    assert a1[1] == 2 && a1[4] == 2 && 4 - 1 == 3;
    // Also check other equal pairs: a[0]=1 and a[2]=1 distance 2, a[3]=2 and a[4]=2 distance 1
    // So max is 3
    assert d1 == 3; // a[1] to a[4]

    // all equal elements case
    var a2 := new int[] [3, 3, 3, 3];
    var d2 := MaxDistEqual(a2);
    assert a2[..] == [3, 3, 3, 3];
    // The maximum distance is between a[0] and a[3], distance 3
    assert a2[0] == 3 && a2[3] == 3 && 3 - 0 == 3;
    assert d2 == 3; // a[0] to a[3]

    // no equal elements case
    var a3 := new int[] [1, 2, 3, 4];
    var d3 := MaxDistEqual(a3);
    assert a3[..] == [1, 2, 3, 4];
    // No equal elements except each element with itself, so maxDist should be 0
    // The postcondition ensures exists i,j with i<=j and a[i]==a[j] and j-i==maxDist
    // For maxDist=0, we can take i=j (any index)
    assert d3 == 0; // a[i] to a[i]
}
