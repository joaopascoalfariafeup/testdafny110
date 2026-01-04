/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures multiset(a[..]) == multiset(old(a[..]))
   decreases *
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursivelly
   }
}


method testRawsort() decreases * {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);

   // Help the verifier connect the postconditions (Sorted + multiset preservation)
   // to the concrete expected outcome.
   assert a.Length == 3;
   assert multiset(a[..]) == multiset([3,5,1]);
   assert multiset([3,5,1]) == multiset([1,3,5]);
   assert multiset(a[..]) == multiset([1,3,5]);
   assert Sorted(a[..]);

   // A sorted length-3 sequence with this multiset must be exactly [1,3,5]
   assert a[0] == 1;
   assert a[1] == 3;
   assert a[2] == 5;

   assert a[..] == [1, 3, 5];
}
