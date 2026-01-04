/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate permutation(a: array<T>, b: array<T>)
  requires a != null && b != null
{
  |a[..]| == |b[..]| &&
  multiset(a[..]) == multiset(b[..])
}

predicate permutationSeq(s: seq<T>, t: seq<T>)
{
  |s| == |t| && multiset(s) == multiset(t)
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures sorted(a[..])
   ensures permutation(old(a[..]), a[..])
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      var oldA := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      RawSort(a); // proceed recursivelly
      assert permutationSeq(oldA, a[..]);
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
