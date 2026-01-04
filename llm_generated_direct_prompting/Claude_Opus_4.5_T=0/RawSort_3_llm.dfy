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
   ensures multiset(a[..]) == old(multiset(a[..]))
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldInversions := Inversions(a);
      ghost var oldMultiset := multiset(a[..]);
      a[i], a[j] := a[j], a[i]; // swap
      assert multiset(a[..]) == oldMultiset;
      assert Inversions(a) < oldInversions by {
         var before := set p, q | 0 <= p < q < a.Length && old(a[p]) > old(a[q]) :: (p, q);
         var after := set p, q | 0 <= p < q < a.Length && a[p] > a[q] :: (p, q);
      }
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
