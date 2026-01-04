// Searches for a value 'x' in an array 'a' and returns an index 
// where x occurs, or -1 if not found. 
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures -1 <= index < a.Length
  ensures index >= 0 ==> a[index] == x
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
{
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != x
  {
    if a[i] == x {
      return i;
    }
  } 
  return -1;
}

method TestLinearSearch() {
  var a := new int[] [3, 2, 1, 3];
  // Helper assertions to help Dafny understand the array contents
  assert a[0] == 3 && a[1] == 2 && a[2] == 1 && a[3] == 3;
  assert a[..] == [3, 2, 1, 3];

  var i := LinearSearch(a, 2);
  // Additional proof helper
  assert forall k :: 0 <= k < 1 ==> a[k] != 2; // a[0] = 3 != 2
  assert a[1] == 2;
  assert i == 1;

  var j := LinearSearch(a, 0);
  // Proof helper for non-existence
  assert a[0] != 0 && a[1] != 0 && a[2] != 0 && a[3] != 0;
  assert j == -1;

  var k := LinearSearch(a, 3);
  // Proof helper for existence
  assert a[0] == 3;
  assert a[3] == 3;
  assert forall k' :: 0 <= k' < 0 ==> a[k'] != 3; // vacuously true
  assert k == 0 || k == 3;
}

