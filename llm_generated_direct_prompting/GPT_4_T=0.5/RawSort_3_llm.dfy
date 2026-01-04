/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparison operators.
type T = int 

// Returns true if the array is sorted in ascending order
predicate sorted(a: array<T>)
{
    forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures sorted(a) && multiset(a[..]) == old(multiset(a[..]))
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursively
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert sorted(a);
   assert a[..] == [1, 3, 5];
}
