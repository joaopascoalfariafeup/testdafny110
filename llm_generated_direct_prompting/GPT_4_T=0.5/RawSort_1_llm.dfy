/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Auxiliary function to check if a sequence is sorted in non-decreasing order.
ghost function IsSorted(s: seq<T>): bool
{
   forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

// Auxiliary function to count the number of occurrences of a value in a sequence.
ghost function Count(s: seq<T>, v: T): nat
{
   if |s| == 0 then 0 else (if s[0] == v then 1 else 0) + Count(s[1..], v)
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures IsSorted(a[..]) // Ensures the array is sorted
   ensures forall v :: 0 <= v < a.Length ==> Count(old(a[..]), a[v]) == Count(a[..], a[v]) // Ensures the array has the same elements as before
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
