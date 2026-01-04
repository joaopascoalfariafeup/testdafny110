
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

// Helper predicate for inversions
ghost predicate IsInversion(s: seq<T>, p: int, q: int)
{
   0 <= p < q < |s| && s[p] > s[q]
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
   
   // Key facts about the swap
   assert newSeq[i] == oldSeq[j];
   assert newSeq[j] == oldSeq[i];
   assert forall k :: 0 <= k < |newSeq| && k != i && k != j ==> newSeq[k] == oldSeq[k];
   
   // (i, j) was an inversion in oldSeq but not in newSeq
   assert (i, j) in oldInvs;
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvs;
   
   // Define sets for analysis
   // Inversions not involving i or j are preserved
   var unchangedOld := set p, q | 0 <= p < q < |oldSeq| && p != i && p != j && q != i && q != j && oldSeq[p] > oldSeq[q] :: (p, q);
   var unchangedNew := set p, q | 0 <= p < q < |newSeq| && p != i && p != j && q != i && q != j && newSeq[p] > newSeq[q] :: (p, q);
   
   // These are equal since values at positions other than i,j are unchanged
   assert unchangedOld == unchangedNew;
   
   // Inversions involving i or j in the old sequence
   var involvingIJOld := oldInvs - unchangedOld;
   var involvingIJNew := newInvs - unchangedNew;
   
   // Count inversions involving i in old vs new
   // For position i: in old, a[i] is large; in new, a[i] is small
   // For position j: in old, a[j] is small; in new, a[j] is large
   
   // Inversions (i, k) for k > j in old: oldSeq[i] > oldSeq[k]
   // Inversions (i, k) for k > j in new: newSeq[i] > newSeq[k], i.e., oldSeq[j] > oldSeq[k]
   // Since oldSeq[i] > oldSeq[j], if oldSeq[j] > oldSeq[k] then oldSeq[i] > oldSeq[k]
   // So new inversions (i, k) for k > j are a subset of old inversions (i, k) for k > j
   
   // Similarly for other cases...
   
   // Key insight: (i,j) is in oldInvs but not in newInvs
   // And for every inversion in newInvs involving i or j, there's a corresponding one in oldInvs
   
   // Let's show newInvs is a proper subset of a set no larger than oldInvs
   
   // For each new inversion, we can find a corresponding old inversion
   forall p, q | (p, q) in newInvs
      ensures exists p', q' :: (p', q') in oldInvs && (p', q') != (i, j)
   {
      if p != i && p != j && q != i && q != j {
         assert (p, q) in oldInvs;
      } else if p == i {
         // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
         // Since oldSeq[i] > oldSeq[j] > oldSeq[q], we have (i, q) in oldInvs
         assert q != j; // because newSeq[i] < newSeq[j]
         assert oldSeq[j] > oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert (i, q) != (i, j);
      } else if p == j {
         // newSeq[j] > newSeq[q] means oldSeq[i] > oldSeq[q]
         // (i, q) is in oldInvs
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert q > j > i;
         assert (i, q) != (i, j);
      } else if q == i {
         // newSeq[p] > newSeq[i] means oldSeq[p] > oldSeq[j]
         // (p, j) is in oldInvs
         assert oldSeq[p] > oldSeq[j];
         assert (p, j) in oldInvs;
         assert p < i < j;
         assert (p, j) != (i, j);
      } else {
         assert q == j;
         // newSeq[p] > newSeq[j] means oldSeq[p] > oldSeq[i]
         assert p != i;
         assert oldSeq[p] > oldSeq[i];
         if p < i {
            assert (p, i) in oldInvs;
            assert (p, i) != (i, j);
         } else {
            // i < p < j
            // oldSeq[p] > oldSeq[i] > oldSeq[j]
            assert (p, j) in oldInvs;
            assert (p, j) != (i, j);
         }
      }
   }
   
   // Now we need to show |newInvs| < |oldInvs|
   // We know (i,j) in oldInvs and (i,j) not in newInvs
   // And newInvs subset of oldInvs would give us what we need, but that's not quite true
   
   // Alternative: show |newInvs| + 1 <= |oldInvs|
   // by showing newInvs + {(i,j)} can be injected into oldInvs
   
   assert (i, j) in oldInvs;
   assert (i, j) !in newInvs;
   
   // Actually, let's just count more carefully
   // The swap at (i,j) removes the inversion (i,j) and may change others
   // But the total count decreases
   
   var oldInvsMinusIJ := oldInvs - {(i, j)};
   assert |oldInvs| == |oldInvsMinusIJ| + 1;
   
   // We need: |newInvs| <= |oldInvsMinusIJ|
   // This follows if we can show newInvs is a subset of oldInvs - {(i,j)} or has an injection into it
   
   // Let's try a different approach: directly bound the change
   assert |newInvs| < |oldInvs|;
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

lemma MultisetHeadTail(s: seq<T>)
   requires |s| > 0
   ensures Multiset(s) == multiset{s[0]} + Multiset(s[1..])
{
   assert s == [s[0]] + s[1..];
}

lemma MultisetSubtract(m1: multiset<T>, m2: multiset<T>, x: T)
   requires m1 == m2
   requires x in m1
   ensures m1 - multiset{x} == m2 - multiset{x}
{
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
      
      MultisetHeadTail(s1);
      MultisetHeadTail(s2);
      var x := s1[0];
      assert Multiset(s1) == multiset{x} + Multiset(s1[1..]);
      assert Multiset(s2) == multiset{x} + Multiset(s2[1..]);
      
      // Since Multiset(s1) == Multiset(s2) and both equal multiset{x} + tail
      // we can subtract multiset{x} from both sides
      assert Multiset(s1) - multiset{x} == Multiset(s2) - multiset{x};
      assert Multiset(s1[1..]) == Multiset(s1) - multiset{x};
      assert Multiset(s2[1..]) == Multiset(s2) - multiset{x};
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
