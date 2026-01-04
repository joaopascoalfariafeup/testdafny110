/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Predicate to check if an array is sorted
ghost predicate Sorted(a: array<T>)
   reads a
{
   forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Multiset of array elements (for proving permutation)
ghost function ArrayMultiset(a: array<T>): multiset<T>
   reads a
{
   multiset(a[..])
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a)
   ensures multiset(a[..]) == multiset(old(a[..]))
   decreases multiset(a[..]), a.Length
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
