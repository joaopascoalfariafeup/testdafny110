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

// Helper function for the mapping - needs explicit bounds for Dafny
ghost function MapInversion(oldSeq: seq<T>, i: int, j: int, p: int, q: int): (int, int)
   requires 0 <= i < j < |oldSeq|
   requires 0 <= p < q < |oldSeq|
{
   if p == i then (i, q)
   else if p == j then (i, q)
   else if q == i then (p, j)
   else if q == j && p < i then (p, i)
   else if q == j && p > i then (p, j)
   else (p, q)
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
   
   // Show that every new inversion maps to an old inversion different from (i,j)
   forall p, q | (p, q) in newInvs
      ensures MapInversion(oldSeq, i, j, p, q) in oldInvs && MapInversion(oldSeq, i, j, p, q) != (i, j)
   {
      var f := MapInversion(oldSeq, i, j, p, q);
      if p != i && p != j && q != i && q != j {
         assert oldSeq[p] == newSeq[p];
         assert oldSeq[q] == newSeq[q];
         assert f == (p, q);
         assert (p, q) in oldInvs;
      } else if p == i {
         assert q > i;
         assert q != j; // since newSeq[i] < newSeq[j]
         assert newSeq[i] == oldSeq[j];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[j] > oldSeq[q];
         assert oldSeq[i] > oldSeq[j] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert f == (i, q);
         assert (i, q) != (i, j);
      } else if p == j {
         assert q > j;
         assert newSeq[j] == oldSeq[i];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvs;
         assert f == (i, q);
         assert (i, q) != (i, j);
      } else if q == i {
         assert p < i;
         assert newSeq[p] == oldSeq[p];
         assert newSeq[i] == oldSeq[j];
         assert oldSeq[p] > oldSeq[j];
         assert (p, j) in oldInvs;
         assert f == (p, j);
         assert (p, j) != (i, j);
      } else {
         assert q == j;
         assert p < j && p != i;
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         assert oldSeq[p] > oldSeq[i];
         if p < i {
            assert (p, i) in oldInvs;
            assert f == (p, i);
            assert (p, i) != (i, j);
         } else {
            assert i < p < j;
            assert oldSeq[p] > oldSeq[i] > oldSeq[j];
            assert (p, j) in oldInvs;
            assert f == (p, j);
            assert (p, j) != (i, j);
         }
      }
   }
   
   // The image of newInvs under MapInversion is a subset of oldInvs - {(i,j)}
   var oldMinusIJ := oldInvs - {(i, j)};
   
   // Build the image set with explicit bounds
   var imageSet := set p, q | 0 <= p < q < |newSeq| && (p, q) in newInvs :: MapInversion(oldSeq, i, j, p, q);
   
   assert imageSet <= oldMinusIJ;
   
   // Show the mapping is injective on newInvs
   forall p1, q1, p2, q2 | (p1, q1) in newInvs && (p2, q2) in newInvs && MapInversion(oldSeq, i, j, p1, q1) == MapInversion(oldSeq, i, j, p2, q2)
      ensures (p1, q1) == (p2, q2)
   {
      var f1 := MapInversion(oldSeq, i, j, p1, q1);
      var f2 := MapInversion(oldSeq, i, j, p2, q2);
      // Case analysis shows injectivity
      if p1 != i && p1 != j && q1 != i && q1 != j {
         assert f1 == (p1, q1);
         if p2 != i && p2 != j && q2 != i && q2 != j {
            assert f2 == (p2, q2);
         } else if p2 == i || p2 == j {
            assert f2.0 == i;
            assert p1 == i;
            assert false;
         } else if q2 == i {
            assert f2.1 == j;
            assert q1 == j;
            assert false;
         } else {
            assert q2 == j;
            if p2 < i { assert f2.1 == i; assert q1 == i; assert false; }
            else { assert f2.1 == j; assert q1 == j; assert false; }
         }
      }
   }
   
   // Since the mapping is injective, |newInvs| <= |imageSet|
   assert |newInvs| <= |imageSet|;
   assert |imageSet| <= |oldMinusIJ|;
   assert |oldMinusIJ| < |oldInvs|;
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

