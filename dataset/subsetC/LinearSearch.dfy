// Searches for a value 'x' in an array 'a' and returns an index 
// where x occurs, or -1 if not found. 
// In case x occurs multiple times, it returns the index of an arbitrary occurrence
// (this holds from a specification perspective; the implementation may choose to follow a more specific policy).
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures 0 <= index < a.Length ==> a[index] == x
  ensures ! (0 <= index < a.Length) ==> index == -1 && x !in a[..]
{
  for i := 0 to a.Length
    invariant  x !in a[..i]
  {
    if a[i] == x {
      return i;
    }
  } 
  return -1;
}

method TestLinearSearch() {
  var a := new int[] [3, 2, 1, 3];
  assert a[..] == [3, 2, 1, 3]; // helper

  var i := LinearSearch(a, 2);
  assert i == 1;

  var j := LinearSearch(a, 0);
  assert j == -1;

  var k := LinearSearch(a, 3);
  assert k == 0 || k == 3;
  //@invalid assert k == 0; // not guaranteed
  //@invalid assert k == 3; // not guaranteed
}