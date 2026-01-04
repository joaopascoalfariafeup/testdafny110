/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

ghost predicate Sorted(s: seq<T>)
{
   forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function Inversions(s: seq<T>): nat
{
   if |s| <= 1 then 0
   else
      (if s[0] > s[|s|-1] then 1 else 0) +
      Inversions(s[..|s|-1]) +
      Inversions(s[1..]) -
      Inversions(s[1..|s|-1])
}

ghost predicate SameElements(s1: seq<T>, s2: seq<T>)
{
   multiset(s1) == multiset(s2)
}

lemma InversionsZeroImpliesSorted(s: seq<T>)
   requires Inversions(s) == 0
   ensures Sorted(s)
{
}

lemma SwapDecreasesInversions(s: seq<T>, i: int, j: int) returns (s': seq<T>)
   requires 0 <= i < j < |s|
   requires s[i] > s[j]
   ensures s' == s[i := s[j]][j := s[i]]
   ensures Inversions(s') < Inversions(s)
   ensures multiset(s') == multiset(s)
{
   s' := s[i := s[j]][j := s[i]];
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures multiset(a[..]) == multiset(old(a[..]))
   decreases Inversions(a[..])
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldSeq := a[..];
      ghost var s' := SwapDecreasesInversions(a[..], i, j);
      a[i], a[j] := a[j], a[i]; // swap
      assert a[..] == s';
      RawSort(a); // proceed recursivelly
   } else {
      assert Sorted(a[..]);
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert Sorted(a[..]);
   assert multiset(a[..]) == multiset{1, 3, 5};
   assert a[..] == [1, 3, 5];
}
