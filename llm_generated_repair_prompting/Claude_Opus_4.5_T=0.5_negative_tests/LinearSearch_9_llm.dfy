// Searches for a value 'x' in an array 'a' and returns an index 
// where x occurs, or -1 if not found. 
// In case x occurs multiple times, it returns the index of an arbitrary occurrence
// (this holds from a specification perspective; the implementation may choose to follow a more specific policy).
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != x
  ensures index >= 0 ==> 0 <= index < a.Length && a[index] == x
  ensures (exists k :: 0 <= k < a.Length && a[k] == x) ==> index >= 0
  ensures index == -1 || index >= 0
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
  assert a[..] == [3, 2, 1, 3];
  assert a[0] == 3 && a[1] == 2 && a[2] == 1 && a[3] == 3;

  var i := LinearSearch(a, 2);
  assert a[1] == 2;
  assert a[0] != 2;
  assert i >= 0 ==> a[i] == 2;
  assert i != -1; // a[1] == 2 so 2 is in array
  assert i >= 0;
  assert 0 <= i < a.Length;
  assert a[i] == 2;
  // Since a[1] is the only element equal to 2, and a[i] == 2, i must be 1
  assert a[0] != 2 && a[2] != 2 && a[3] != 2;
  assert i == 1;

  var j := LinearSearch(a, 0);
  assert a[0] != 0 && a[1] != 0 && a[2] != 0 && a[3] != 0;
  assert forall m :: 0 <= m < a.Length ==> a[m] != 0;
  // If j >= 0, then a[j] == 0, but we know all elements != 0
  assert j >= 0 ==> a[j] == 0;
  assert j >= 0 ==> 0 <= j < a.Length;
  assert j >= 0 ==> a[j] != 0; // from our assertion about all elements
  assert j >= 0 ==> false;
  assert j < 0;
  assert j == -1 || j >= 0;
  assert j == -1;

  var k := LinearSearch(a, 3);
  assert a[0] == 3 && a[3] == 3;
  assert k >= 0 ==> a[k] == 3;
  // Since a[0] == 3, k must be >= 0
  assert k != -1; // a[0] == 3 so 3 is in array
  assert k >= 0;
  assert 0 <= k < a.Length;
  assert a[k] == 3;
  // k could be 0 or 3 since both have value 3
  assert k == 0 || k == 3;
  //@invalid assert k == 0; // not guaranteed
  //@invalid assert k == 3; // not guaranteed
}
