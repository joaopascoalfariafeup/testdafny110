/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

// Predicate that checks if an array is sorted
ghost predicate Sorted(a: array<T>)
   reads a
{
   forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Predicate that checks if one sequence is a permutation of another
ghost predicate IsPermutation(s1: seq<T>, s2: seq<T>)
{
   multiset(s1) == multiset(s2)
}

// Count of inversions (pairs out of order) - used for termination
ghost function Inversions(a: array<T>): nat
   reads a
{
   |set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)|
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a)
   ensures IsPermutation(a[..], old(a[..]))
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldInversions := Inversions(a);
      ghost var oldSeq := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert multiset(a[..]) == multiset(oldSeq);
      assert Inversions(a) < oldInversions;
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
