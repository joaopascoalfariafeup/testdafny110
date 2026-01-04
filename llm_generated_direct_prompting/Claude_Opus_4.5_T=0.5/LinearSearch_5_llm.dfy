// Searches for a value 'x' in an array 'a' and returns an index 
// where x occurs, or -1 if not found. 
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures -1 <= index < a.Length
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != x
  ensures index >= 0 ==> a[index] == x
  ensures index >= 0 ==> forall k :: 0 <= k < index ==> a[k] != x
{
  for i := 0 to a.Length
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

  var i := LinearSearch(a, 2);
  assert i == 1;

  var j := LinearSearch(a, 0);
  assert j == -1;

  var k := LinearSearch(a, 3);
  assert k == 0 || k == 3;
}
