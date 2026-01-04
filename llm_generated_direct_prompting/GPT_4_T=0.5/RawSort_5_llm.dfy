/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Ghost function to check if a sequence is sorted
ghost function IsSorted(s: seq<T>): bool
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures IsSorted(a[..]) // Ensures that the array is sorted after the method
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
