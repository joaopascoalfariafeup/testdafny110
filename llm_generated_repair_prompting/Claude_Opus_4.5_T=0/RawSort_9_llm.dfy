
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

// Map each new inversion to a corresponding old inversion
ghost function MapInversion(oldSeq: seq<T>, newSeq: seq<T>, i: int, j: int, inv: (int, int)): (int, int)
   requires 0 <= i < j < |oldSeq|
   requires |newSeq| == |oldSeq|
   requires oldSeq[i] > oldSeq[j]
   requires newSeq == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   requires inv in InversionSet(newSeq)
{
   var p := inv.0;
   var q := inv.1;
   if p != i && p != j && q != i && q != j then inv
   else if p == i then (i, q)  // oldSeq[i] > oldSeq[j] > oldSeq[q]
   else if p == j then (i, q)  // oldSeq[i] > oldSeq[q]
   else if q == i then (p, j)  // oldSeq[p] > oldSeq[j]
   else if p < i then (p, i)   // q == j, p < i: oldSeq[p] > oldSeq[i]
   else (p, j)                  // q == j, i < p < j: oldSeq[p] > oldSeq[i] > oldSeq[j]
}

lemma MapInversionValid(oldSeq: seq<T>, newSeq: seq<T>, i: int, j: int, inv: (int, int))
   requires 0 <= i < j < |oldSeq|
   requires |newSeq| == |oldSeq|
   requires oldSeq[i] > oldSeq[j]
   requires newSeq == oldSeq[i := oldSeq[j]][j := oldSeq[i]]
   requires inv in InversionSet(newSeq)
   ensures MapInversion(oldSeq, newSeq, i, j, inv) in InversionSet(oldSeq)
   ensures MapInversion(oldSeq, newSeq, i, j, inv) != (i, j)
{
   var p := inv.0;
   var q := inv.1;
   var mapped := MapInversion(oldSeq, newSeq, i, j, inv);
   
   if p != i && p != j && q != i && q != j {
      assert newSeq[p] == oldSeq[p] && newSeq[q] == oldSeq[q];
      assert oldSeq[p] > oldSeq[q];
      assert mapped == inv;
      assert mapped in InversionSet(oldSeq);
      assert mapped != (i, j);
   } else if p == i {
      assert q != j; // because newSeq[i] < newSeq[j]
      assert newSeq[i] > newSeq[q];
      assert oldSeq[j] > oldSeq[q];
      assert oldSeq[i] > oldSeq[j] > oldSeq[q];
      assert mapped == (i, q);
      assert mapped in InversionSet(oldSeq);
      assert mapped != (i, j);
   } else if p == j {
      assert newSeq[j] > newSeq[q];
      assert oldSeq[i] > oldSeq[q];
      assert mapped == (i, q);
      assert q > j > i;
      assert mapped in InversionSet(oldSeq);
      assert mapped != (i, j);
   } else if q == i {
      assert newSeq[p] > newSeq[i];
      assert oldSeq[p] > oldSeq[j];
      assert mapped == (p, j);
      assert p < i < j;
      assert mapped in InversionSet(oldSeq);
      assert mapped != (i, j);
   } else {
      assert q == j;
      assert p != i;
      assert newSeq[p] > newSeq[j];
      assert oldSeq[p] > oldSeq[i];
      if p < i {
         assert mapped == (p, i);
         assert mapped in InversionSet(oldSeq);
         assert mapped != (i, j);
      } else {
         assert i < p < j;
         assert oldSeq[p] > oldSeq[i] > oldSeq[j];
         assert mapped == (p, j);
         assert mapped in InversionSet(oldSeq);
         assert mapped != (i, j);
      }
   }
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
   
   // (i, j) was an inversion in oldSeq but not in newSeq
   assert (i, j) in oldInvs;
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvs;
   
   var oldInvsMinusIJ := oldInvs - {(i, j)};
   assert |oldInvs| == |oldInvsMinusIJ| + 1;
   
   // Show that each new inversion maps to a distinct old inversion (not (i,j))
   forall inv | inv in newInvs
      ensures MapInversion(oldSeq, newSeq, i, j, inv) in oldInvsMinusIJ
   {
      MapInversionValid(oldSeq, newSeq, i, j, inv);
      var mapped := MapInversion(oldSeq, newSeq, i, j, inv);
      assert mapped in oldInvs && mapped != (i, j);
      assert mapped in oldInvsMinusIJ;
   }
   
   // The mapping is injective
   forall inv1, inv2 | inv1 in newInvs && inv2 in newInvs && inv1 != inv2
      ensures MapInversion(oldSeq, newSeq, i, j, inv1) != MapInversion(oldSeq, newSeq, i, j, inv2)
   {
      var p1, q1 := inv1.0, inv1.1;
      var p2, q2 := inv2.0, inv2.1;
      var m1 := MapInversion(oldSeq, newSeq, i, j, inv1);
      var m2 := MapInversion(oldSeq, newSeq, i, j, inv2);
      
      // Case analysis shows the mapping preserves distinctness
      if p1 != i && p1 != j && q1 != i && q1 != j {
         assert m1 == inv1;
         if p2 != i && p2 != j && q2 != i && q2 != j {
            assert m2 == inv2;
         }
      }
   }
   
   // Since we have an injection from newInvs to oldInvsMinusIJ
   var mappedSet := set inv | inv in newInvs :: MapInversion(oldSeq, newSeq, i, j, inv);
   assert mappedSet <= oldInvsMinusIJ;
   assert |mappedSet| == |newInvs|;
   assert |newInvs| <= |oldInvsMinusIJ|;
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

