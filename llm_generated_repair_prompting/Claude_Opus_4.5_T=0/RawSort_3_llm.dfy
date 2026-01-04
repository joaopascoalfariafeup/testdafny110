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
   assert newSeq[i] == oldSeq[j];
   assert newSeq[j] == oldSeq[i];
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvs;
   
   // Show that every new inversion was an old inversion (except (i,j) which is gone)
   forall p, q | 0 <= p < q < |newSeq| && newSeq[p] > newSeq[q]
      ensures (p, q) in oldInvs
   {
      if p == i && q == j {
         // This case is impossible since newSeq[i] < newSeq[j]
         assert false;
      } else if p == i && q != j {
         // newSeq[i] = oldSeq[j], newSeq[q] = oldSeq[q]
         assert newSeq[i] == oldSeq[j];
         assert newSeq[q] == oldSeq[q];
         // newSeq[i] > newSeq[q] means oldSeq[j] > oldSeq[q]
         if q > j {
            // (j, q) was an inversion in old, but we need (i, q) in oldInvs
            // oldSeq[i] > oldSeq[j] > oldSeq[q], so (i, q) was inversion
            assert oldSeq[i] > oldSeq[j] > oldSeq[q];
            assert (i, q) in oldInvs;
         } else {
            // q < j, and oldSeq[j] > oldSeq[q]
            // oldSeq[i] > oldSeq[j] > oldSeq[q], so (i, q) was inversion
            assert oldSeq[i] > oldSeq[q];
            assert (i, q) in oldInvs;
         }
      } else if p == j {
         // newSeq[j] = oldSeq[i], newSeq[q] = oldSeq[q]
         assert newSeq[j] == oldSeq[i];
         assert newSeq[q] == oldSeq[q];
         // newSeq[j] > newSeq[q] means oldSeq[i] > oldSeq[q]
         // So (i, q) was an inversion if i < q, which is true since i < j < q
         assert i < q;
         assert (i, q) in oldInvs;
      } else if q == i {
         // p < q = i, so p < i
         assert newSeq[p] == oldSeq[p];
         assert newSeq[i] == oldSeq[j];
         // newSeq[p] > newSeq[i] means oldSeq[p] > oldSeq[j]
         // So (p, j) was an inversion since p < i < j
         assert p < j;
         assert (p, j) in oldInvs;
      } else if q == j {
         // p < j and p != i
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         // newSeq[p] > newSeq[j] means oldSeq[p] > oldSeq[i]
         if p < i {
            // (p, i) was an inversion
            assert (p, i) in oldInvs;
         } else {
            // p > i, so i < p < j
            // oldSeq[p] > oldSeq[i] and we need to find an old inversion
            // Actually (p, j) might be an inversion: oldSeq[p] > oldSeq[i] > oldSeq[j]
            assert oldSeq[p] > oldSeq[i] > oldSeq[j];
            assert (p, j) in oldInvs;
         }
      } else {
         // p, q are neither i nor j
         assert newSeq[p] == oldSeq[p];
         assert newSeq[q] == oldSeq[q];
         assert (p, q) in oldInvs;
      }
   }
   
   assert newInvs <= oldInvs;
   assert (i, j) in oldInvs && (i, j) !in newInvs;
   assert newInvs <= oldInvs - {(i, j)};
   assert |newInvs| <= |oldInvs - {(i, j)}|;
   assert |oldInvs - {(i, j)}| == |oldInvs| - 1;
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
      // s1[0] is minimum of s1, s2[0] is minimum of s2
      // Since s1[0] in s2 and s2 is sorted, s1[0] >= s2[0]
      // Since s2[0] in s1 and s1 is sorted, s2[0] >= s1[0]
      assert s1[0] <= s2[0] && s2[0] <= s1[0];
      assert s1[0] == s2[0];
      
      MultisetHeadTail(s1);
      MultisetHeadTail(s2);
      assert Multiset(s1) == multiset{s1[0]} + Multiset(s1[1..]);
      assert Multiset(s2) == multiset{s2[0]} + Multiset(s2[1..]);
      assert multiset{s1[0]} == multiset{s2[0]};
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

