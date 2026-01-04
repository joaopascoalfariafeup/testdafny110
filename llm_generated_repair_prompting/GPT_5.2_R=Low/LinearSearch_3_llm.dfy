// Searches for a value 'x' in an array 'a' and returns an index
// where x occurs, or -1 if not found.
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  requires a != null
  ensures index == -1 || 0 <= index < a.Length
  ensures 0 <= index < a.Length ==> a[index] == x
  // If found, it is the *first* occurrence
  ensures 0 <= index < a.Length ==> (forall k :: 0 <= k < index ==> a[k] != x)
  // Found iff there exists an occurrence
  ensures index == -1 <==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
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
  assert a[..] == [3, 2, 1, 3];
  // Help the verifier use concrete element facts
  assert a[0] == 3 && a[1] == 2 && a[2] == 1 && a[3] == 3;

  var i := LinearSearch(a, 2);
  assert i == 1;

  var j := LinearSearch(a, 0);
  assert j == -1;

  var k := LinearSearch(a, 3);
  assert k == 0 || k == 3;
}

