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

ghost function Inversions(a: array<T>): nat
   reads a
{
   |set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)|
}

ghost function InversionSet(a: array<T>): set<(int, int)>
   reads a
{
   set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)
}

ghost function SeqInversionSet(s: seq<T>): set<(int, int)>
{
   set p, q | 0 <= p < q < |s| && s[p] > s[q] :: (p, q)
}

lemma SwapDecreasesInversions(a: array<T>, i: int, j: int, oldSeq: seq<T>)
   requires 0 <= i < j < a.Length
   requires |oldSeq| == a.Length
   requires oldSeq[i] > oldSeq[j]
   requires a[..] == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   ensures Inversions(a) < |SeqInversionSet(oldSeq)|
{
   var newSeq := a[..];
   var oldInvSet := SeqInversionSet(oldSeq);
   var newInvSet := InversionSet(a);
   
   // The pair (i, j) was an inversion in old but not in new
   assert (i, j) in oldInvSet;
   assert newSeq[i] == oldSeq[j];
   assert newSeq[j] == oldSeq[i];
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvSet;
   
   // Show that newInvSet is a subset of oldInvSet minus (i,j)
   forall p, q | (p, q) in newInvSet
      ensures (p, q) in oldInvSet
   {
      assert 0 <= p < q < a.Length;
      assert a[p] > a[q];
      if p != i && p != j && q != i && q != j {
         assert oldSeq[p] == newSeq[p] && oldSeq[q] == newSeq[q];
         assert oldSeq[p] > oldSeq[q];
      } else if p == i && q == j {
         assert false; // This case is impossible since (i,j) not in newInvSet
      } else if p == i && q != j {
         // newSeq[i] = oldSeq[j], newSeq[q] = oldSeq[q]
         // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
         if q < j {
            assert oldSeq[j] > oldSeq[q];
            assert (q, j) in oldInvSet;
            // Need to show (p, q) = (i, q) maps to something in oldInvSet
            // Actually we need (i, q) in oldInvSet
            // This requires oldSeq[i] > oldSeq[q]
            // We know oldSeq[j] > oldSeq[q] and oldSeq[i] > oldSeq[j]
            assert oldSeq[i] > oldSeq[j] > oldSeq[q];
         } else {
            // q > j, so newSeq[q] = oldSeq[q]
            // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
            // oldSeq[i] > oldSeq[j] > oldSeq[q]
            assert oldSeq[i] > oldSeq[q];
         }
      } else if p == j {
         // newSeq[j] = oldSeq[i]
         // newSeq[j] > newSeq[q] means oldSeq[i] > newSeq[q]
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
      } else if q == i {
         // p < i, newSeq[p] = oldSeq[p], newSeq[i] = oldSeq[j]
         assert oldSeq[p] > oldSeq[j];
      } else if q == j {
         // p < j, p != i, newSeq[p] = oldSeq[p], newSeq[j] = oldSeq[i]
         assert oldSeq[p] > oldSeq[i];
      }
   }
   
   assert newInvSet <= oldInvSet - {(i, j)};
   assert |newInvSet| <= |oldInvSet - {(i, j)}|;
   assert |oldInvSet - {(i, j)}| == |oldInvSet| - 1;
   assert |newInvSet| < |oldInvSet|;
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
      ghost var oldInvSet := SeqInversionSet(oldSeq);
      assert oldInv == |oldInvSet|;
      a[i], a[j] := a[j], a[i]; // swap
      assert Multiset(a[..]) == oldMultiset;
      SwapDecreasesInversions(a, i, j, oldSeq);
      assert Inversions(a) < |oldInvSet|;
      assert Inversions(a) < oldInv;
      RawSort(a); // proceed recursivelly
   }
}

lemma MultisetTailLemma(s: seq<T>)
   requires |s| > 0
   ensures multiset(s[1..]) == multiset(s) - multiset{s[0]}
{
   assert s == [s[0]] + s[1..];
   assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
}

lemma SortedMultisetUnique(s1: seq<T>, s2: seq<T>)
   requires Sorted(s1)
   requires Sorted(s2)
   requires Multiset(s1) == Multiset(s2)
   ensures s1 == s2
{
   if s1 == [] {
      assert |Multiset(s2)| == 0;
   } else if s2 == [] {
      assert |Multiset(s1)| == 0;
   } else {
      assert s1[0] in Multiset(s1);
      assert s2[0] in Multiset(s2);
      assert s1[0] in Multiset(s2);
      assert s2[0] in Multiset(s1);
      // Both are sorted, so s1[0] is min of s1 and s2[0] is min of s2
      // Since they have same multiset, mins must be equal
      assert forall k :: 0 <= k < |s1| ==> s1[0] <= s1[k];
      assert forall k :: 0 <= k < |s2| ==> s2[0] <= s2[k];
      assert s1[0] == s2[0];
      MultisetTailLemma(s1);
      MultisetTailLemma(s2);
      assert Multiset(s1[1..]) == Multiset(s1) - multiset{s1[0]};
      assert Multiset(s2[1..]) == Multiset(s2) - multiset{s2[0]};
      SortedMultisetUnique(s1[1..], s2[1..]);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   ghost var oldSeq := a[..];
   assert oldSeq == [3, 5, 1];
   RawSort(a);
   assert Sorted(a[..]);
   assert Multiset(a[..]) == Multiset(oldSeq);
   assert Multiset(oldSeq) == multiset{3, 5, 1};
   assert Sorted([1, 3, 5]);
   assert Multiset([1, 3, 5]) == multiset{1, 3, 5};
   assert multiset{3, 5, 1} == multiset{1, 3, 5};
   SortedMultisetUnique(a[..], [1, 3, 5]);
   assert a[..] == [1, 3, 5];
}
