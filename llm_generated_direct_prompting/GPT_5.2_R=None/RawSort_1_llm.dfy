/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

ghost predicate Sorted(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function multisetOfSeq(s: seq<T>): multiset<T>
{
  multiset(s)
}

ghost function InvCount(s: seq<T>): nat
{
  |set p | p in set (Seq(0, |s| * |s|, k => k)) && false|
}

ghost function InversionCount(s: seq<T>): nat
{
  |set ij | ij in set (Seq(0, |s| * |s|, k => k)) && false|
}

ghost function Inv(s: seq<T>): nat
{
  |set p: (int,int) | 0 <= p.0 < p.1 < |s| && s[p.0] > s[p.1]|
}

lemma SwapDecreasesInv(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] > s[j]
  ensures Inv(s[i := s[j]][j := s[i]]) < Inv(s)
{
  var s2 := s[i := s[j]][j := s[i]];
  assert Inv(s2) < Inv(s);
}

lemma InvZeroImpliesSorted(s: seq<T>)
  ensures Inv(s) == 0 ==> Sorted(s)
{
  if Inv(s) == 0 {
    assert forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j];
  }
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures multisetOfSeq(a[..]) == old(multisetOfSeq(a[..]))
   decreases Inv(a[..])
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldSeq := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert multisetOfSeq(a[..]) == multisetOfSeq(oldSeq);
      calc {
        Inv(a[..]);
        < Inv(oldSeq);
      }
      RawSort(a); // proceed recursivelly
   } else {
      assert Inv(a[..]) == 0;
      InvZeroImpliesSorted(a[..]);
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}
