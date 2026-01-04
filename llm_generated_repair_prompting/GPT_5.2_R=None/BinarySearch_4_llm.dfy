/*  
* Formal verification of the binary search algorithm in Dafny. 
*/

type T = int // for demo purposes, but could be another type 

ghost predicate Sorted(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

  
// Finds a value 'x' in a sorted array 'a', and returns its index, or -1 if not found. 
method BinarySearch(a: array<T>, x: T) returns (index: int)
  requires Sorted(a)
  ensures index == -1 ==> (forall i :: 0 <= i < a.Length ==> a[i] != x)
  ensures 0 <= index ==> index < a.Length && a[index] == x
  ensures (exists i :: 0 <= i < a.Length && a[i] == x) ==> 0 <= index
{   
  var low, high := 0, a.Length;
  while low < high 
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < x
    invariant forall i :: high <= i < a.Length ==> x < a[i]
  {
    var mid := low + (high - low) / 2;
    assert low <= mid < high;
    if {
      case a[mid]  < x =>
        low := mid + 1;
      case a[mid]  > x =>
        high := mid; 
      case a[mid] == x =>
        return mid;
    }
  }
  assert low == high;
  assert forall i :: 0 <= i < a.Length ==> a[i] != x;
  return -1;
}

// Simple test cases to check the post-condition.
method TestBinarySearch() {
  var a := new int[4] [1, 4, 4, 6];
  assert Sorted(a); // needed to call BinarySearch
  assert a[..] == [1, 4, 4, 6]; // help the verifier with concrete contents

  // found case
  var id1 := BinarySearch(a, 1); 
  assert a[0] == 1;
  assert id1 == 0;
  
  // not found case
  var id2 := BinarySearch(a, 3); 
  // help prove "not found": show 3 is not in this concrete array
  assert forall i :: 0 <= i < a.Length ==> a[i] != 3;
  // use BinarySearch postcondition to connect the above fact to the result
  assert id2 == -1 || a[id2] == 3;
  assert id2 == -1; 
  
  // duplicate case
  var id3 := BinarySearch(a, 4); 
  assert a[1] == a[2] == 4;
  assert id3 == 1 || id3 == 2;
  //@invalid: assert id3 == 1; // cannot be guaranteed
  //@invalid: assert id3 == 2; // cannot be guaranteed

  // precondition violation
  var b := new int[2] [2, 1];
  //@invalid var _ := BinarySearch(b, 1); // b is not sorted
} 

