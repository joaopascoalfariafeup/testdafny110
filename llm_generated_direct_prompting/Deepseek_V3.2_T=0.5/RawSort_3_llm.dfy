/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate sorted(s: seq<T>)
{
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

predicate permutation(a: array<T>, s: seq<T>)
  requires a != null
{
  |s| == a.Length &&
  (multiset(s[..]) == multiset(old(a[..])))
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures sorted(a[..])
   ensures permutation(a, a[..])
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
