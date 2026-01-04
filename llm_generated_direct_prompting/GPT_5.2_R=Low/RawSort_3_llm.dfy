/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate Sorted(s: seq<T>)
{
  forall i: int, j: int :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma LemmaNoInversionImpliesSorted(s: seq<T>)
  ensures (!exists i: int, j: int :: 0 <= i < j < |s| && s[i] > s[j]) ==> Sorted(s)
{
}

lemma LemmaMultisetSwap(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]) == multiset(s)
{
}

lemma LemmaSwapSeqMultiset(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
  var t := s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..];
  assert t == s;
  calc {
    multiset(s[i := s[j]][j := s[i]]);
    == { }
    multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]);
    == { LemmaMultisetSwap(s, i, j) }
    multiset(s);
  }
}


// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures multiset(a[..]) == multiset(old(a[..]))
   decreases *
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      a[i], a[j] := a[j], a[i]; // swap

      assert multiset(a[..]) == multiset(old(a[..])) by {
        LemmaSwapSeqMultiset(old(a[..]), i, j);
      }

      RawSort(a); // proceed recursivelly

      assert multiset(a[..]) == multiset(old(a[..])) by {
        assert multiset(a[..]) == multiset(old(multiset(a[..])));
        assert old(multiset(a[..])) == multiset(old(a[..]));
      }
   } else {
      assert Sorted(a[..]) by {
        LemmaNoInversionImpliesSorted(a[..]);
      }
      assert multiset(a[..]) == multiset(old(a[..])) by {
        assert a[..] == old(a[..]);
      }
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
