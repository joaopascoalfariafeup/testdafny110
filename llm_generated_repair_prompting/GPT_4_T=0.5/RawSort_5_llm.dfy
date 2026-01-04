
```dafny
/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Checks whether an array is sorted in non-decreasing order.
predicate IsSorted(a: array<T>)
   reads a
{
    forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
}

// Function to calculate the number of inversions in the array
ghost function Inversions(a: array<T>): nat
  reads a
{
  (| forall i, j :: 0 <= i < j < a.Length && a[i] > a[j] |)
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures IsSorted(a)
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursively
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert IsSorted(a);
}
```

