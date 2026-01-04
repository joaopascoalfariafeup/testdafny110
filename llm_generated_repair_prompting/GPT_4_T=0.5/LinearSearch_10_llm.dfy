
// Searches for a value 'x' in an array 'a' and returns the index 
// of the first occurrence of x, or -1 if not found. 
method LinearSearch<T(==)>(a: array<T>, x: T) returns (index: int)
  ensures 0 <= index < a.Length ==> a[index] == x
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> a[k] != x)
  ensures 0 <= index < a.Length ==> (forall k :: 0 <= k < index ==> a[k] != x)
  ensures (exists k :: 0 <= k < a.Length && a[k] == x) ==> index != -1
  ensures (!exists k :: 0 <= k < a.Length && a[k] == x) ==> index == -1
{
  index := -1;
  for i := 0 to a.Length
    invariant (forall k :: 0 <= k < i ==> a[k] != x) || (index != -1 && a[index] == x)
    invariant index == -1 || (0 <= index < i && a[index] == x)
    invariant index == -1 || (forall k :: 0 <= k < index ==> a[k] != x)
  {
    if a[i] == x {
      index := i;
      return;
    }
  } 
}

method TestLinearSearch() {
  var a := new int[] [3, 2, 1, 3];
  assert a[..] == [3, 2, 1, 3]; // helper assertion

  var i := LinearSearch(a, 2);
  assert i == 1;
  assert a[i] == 2; // helper assertion

  var j := LinearSearch(a, 0);
  assert j == -1;
  assert forall k :: 0 <= k < a.Length ==> a[k] != 0; // helper assertion

  var k := LinearSearch(a, 3);
  assert k == 0;
  assert a[k] == 3; // helper assertion
  assert forall m :: 0 <= m < k ==> a[m] != 3; // helper assertion
}

