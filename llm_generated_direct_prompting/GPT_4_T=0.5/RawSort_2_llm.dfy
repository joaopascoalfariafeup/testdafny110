/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Auxiliary ghost function to check if an array is sorted
ghost function IsSorted(a: array<T>): bool
{
    forall k :: 0 <= k < a.Length - 1 ==> a[k] <= a[k+1]
}

// Auxiliary ghost function to count the number of occurrences of a value in an array
ghost function Count(a: array<T>, val: T): nat
{
    if a == null then 0 else
    if a.Length == 0 then 0 else
    if a[0] == val then 1 + Count(a[1..], val) else Count(a[1..], val)
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures IsSorted(a) // The array is sorted after the method
   ensures forall k :: 0 <= k < a.Length ==> Count(a, a[k]) == old(Count(a, a[k])) // The count of each element in the array is preserved 
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursively
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
