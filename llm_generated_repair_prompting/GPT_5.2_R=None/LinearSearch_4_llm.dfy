// Searches for a value 'x' in an array 'a' and returns an index
// where x occurs, or -1 if not found.
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures index == -1 || 0 <= index < a.Length
  ensures index != -1 ==> a[index] == x
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
  // If x occurs, this implementation returns the *first* occurrence
  ensures index != -1 ==> (forall k :: 0 <= k < index ==> a[k] != x)
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

  var i := LinearSearch(a, 2);
  // Help the verifier connect i with the concrete first-occurrence fact in this array
  assert a[0] != 2;
  assert a[1] == 2;
  assert i != -1; // since 2 occurs
  assert i == 1;  // by "first occurrence" postcondition

  var j := LinearSearch(a, 0);
  assert j == -1;

  var k := LinearSearch(a, 3);
  // Help the verifier connect k with the concrete first-occurrence fact in this array
  assert a[0] == 3;
  assert k != -1; // since 3 occurs
  assert k == 0;  // by "first occurrence" postcondition
}
