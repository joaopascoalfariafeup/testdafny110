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
  ensures -1 <= index < a.Length
  ensures index >= 0 ==> a[index] == x
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != x
{   
  var low, high := 0, a.Length;
  while low < high 
    invariant 0 <= low <= high <= a.Length
    invariant forall k :: 0 <= k < low ==> a[k] < x
    invariant forall k :: high <= k < a.Length ==> a[k] > x
  {
    var mid := low + (high - low) / 2;
    if {
      case a[mid]  < x => low := mid + 1;
      case a[mid]  > x => high := mid; 
      case a[mid] == x => return mid;
    }
  }
  return -1;
}

// Simple test cases to check the post-condition.
method TestBinarySearch() {
  var a := new int[4] [1, 4, 4, 6];
  
  // found case
  var id1 := BinarySearch(a, 1); 
  assert a[0] == 1;
  assert id1 == 0;
  
  // not found case
  var id2 := BinarySearch(a, 3); 
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