/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

ghost predicate Sorted(s: seq<T>)
{
   forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function Multiset(s: seq<T>): multiset<T>
{
   multiset(s)
}

ghost function InversionSet(a: seq<T>): set<(int, int)>
{
   set i, j | 0 <= i < j < |a| && a[i] > a[j] :: (i, j)
}

ghost function Inversions(a: array<T>): nat
   reads a
{
   |InversionSet(a[..])|
}

lemma SwapDecreasesInversions(a: array<T>, i: int, j: int, oldSeq: seq<T>)
   requires 0 <= i < j < a.Length
   requires |oldSeq| == a.Length
   requires oldSeq[i] > oldSeq[j]
   requires a[..] == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   ensures |InversionSet(a[..])| < |InversionSet(oldSeq)|
{
   var newSeq := a[..];
   var oldInvs := InversionSet(oldSeq);
   var newInvs := InversionSet(newSeq);
   
   // The pair (i, j) was an inversion in oldSeq but not in newSeq
   assert (i, j) in oldInvs;
   assert (i, j) !in newInvs;
   
   // We'll show that newInvs is a subset of oldInvs minus (i,j) plus at most |oldInvs| - 1 elements
   // Actually, we show newInvs subset of (oldInvs - {(i,j)}) which gives us the result
   
   forall p, q | 0 <= p < q < |newSeq| && newSeq[p] > newSeq[q]
      ensures (p, q) in oldInvs || (p, q) == (i, j)
   {
      if p == i && q == j {
         // This case is impossible since newSeq[i] <= newSeq[j]
         assert newSeq[i] == oldSeq[j];
         assert newSeq[j] == oldSeq[i];
         assert oldSeq[i] > oldSeq[j];
         assert newSeq[i] < newSeq[j];
         assert false;
      } else if p == i {
         // newSeq[i] = oldSeq[j], newSeq[q] = oldSeq[q] (q != j since q > i and q != j means q > j or q < j, but q > i and q != j)
         if q != j {
            assert newSeq[i] == oldSeq[j];
            assert newSeq[q] == oldSeq[q];
            // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
            // So (j, q) was an inversion if j < q, or (q, j) if q < j
            if q > j {
               assert (j, q) in oldInvs;
            } else {
               // q < j, and oldSeq[j] > oldSeq[q], so (q, j) is inversion if oldSeq[q] > oldSeq[j] - no
               // We have oldSeq[j] > oldSeq[q], so not (q,j) inversion
               // But we need to show (p,q) = (i,q) relates to old inversions
               // oldSeq[i] > oldSeq[j] > oldSeq[q], so (i, q) was inversion in old
               assert oldSeq[i] > oldSeq[q];
               assert (i, q) in oldInvs;
            }
         }
      } else if p == j {
         assert newSeq[j] == oldSeq[i];
         assert newSeq[q] == oldSeq[q];
         assert (j, q) in oldInvs || (i, q) in oldInvs;
      } else if q == i {
         // impossible since p < q and p != i means p < i = q
         assert newSeq[p] == oldSeq[p];
         assert newSeq[i] == oldSeq[j];
         assert (p, j) in oldInvs || (p, i) in oldInvs;
      } else if q == j {
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         assert (p, i) in oldInvs || (p, j) in oldInvs;
      } else {
         assert newSeq[p] == oldSeq[p];
         assert newSeq[q] == oldSeq[q];
         assert (p, q) in oldInvs;
      }
   }
   
   assert newInvs <= oldInvs - {(i, j)};
   assert |newInvs| <= |oldInvs - {(i, j)}| < |oldInvs|;
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures Multiset(a[..]) == Multiset(old(a[..]))
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldInv := Inversions(a);
      ghost var oldMultiset := Multiset(a[..]);
      ghost var oldSeq := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert Multiset(a[..]) == oldMultiset;
      SwapDecreasesInversions(a, i, j, oldSeq);
      assert Inversions(a) < oldInv;
      RawSort(a); // proceed recursivelly
   }
}

lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
   requires Sorted(s1) && Sorted(s2)
   requires Multiset(s1) == Multiset(s2)
   ensures s1 == s2
{
   if s1 == [] {
      assert |Multiset(s2)| == 0;
      assert s2 == [];
   } else if s2 == [] {
      assert |Multiset(s1)| == 0;
      assert s1 == [];
   } else {
      assert s1[0] in Multiset(s1);
      assert s1[0] in Multiset(s2);
      assert s1[0] in s2;
      assert s2[0] in Multiset(s2);
      assert s2[0] in Multiset(s1);
      assert s2[0] in s1;
      assert s1[0] <= s2[0] && s2[0] <= s1[0];
      assert s1[0] == s2[0];
      assert Multiset(s1[1..]) == Multiset(s2[1..]);
      SortedMultisetUnique(s1[1..], s2[1..]);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   assert a[..] == [3, 5, 1];
   ghost var oldMultiset := Multiset(a[..]);
   RawSort(a);
   assert Sorted(a[..]);
   assert Multiset(a[..]) == oldMultiset;
   assert Sorted([1, 3, 5]);
   assert Multiset([1, 3, 5]) == oldMultiset;
   SortedMultisetUnique(a[..], [1, 3, 5]);
   assert a[..] == [1, 3, 5];
}
