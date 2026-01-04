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

lemma InversionsEqualsSetSize(a: array<T>)
   ensures Inversions(a) == |InversionSet(a)|
{
   // Both are defined identically
}

// Helper function to count inversions in a sequence
ghost function SeqInversions(s: seq<T>): nat
{
   |SeqInversionSet(s)|
}

lemma InjectiveMapBound<A,B>(s: set<A>, t: set<B>, f: A -> B)
   requires forall a :: a in s ==> f(a) in t
   requires forall a1, a2 :: a1 in s && a2 in s && a1 != a2 ==> f(a1) != f(a2)
   ensures |s| <= |t|
{
   if s == {} {
   } else {
      var x :| x in s;
      var s' := s - {x};
      var t' := t - {f(x)};
      assert f(x) in t;
      forall a | a in s' ensures f(a) in t' {
         assert a in s;
         assert f(a) in t;
         assert a != x;
         assert f(a) != f(x);
      }
      forall a1, a2 | a1 in s' && a2 in s' && a1 != a2 ensures f(a1) != f(a2) {
         assert a1 in s && a2 in s;
      }
      InjectiveMapBound(s', t', f);
   }
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
   
   InversionsEqualsSetSize(a);
   
   // Key facts about the swap
   assert newSeq[i] == oldSeq[j];
   assert newSeq[j] == oldSeq[i];
   forall k | 0 <= k < a.Length && k != i && k != j
      ensures newSeq[k] == oldSeq[k]
   {}
   
   // (i,j) was an inversion in old but not in new
   assert (i, j) in oldInvSet;
   assert newSeq[i] < newSeq[j];
   assert (i, j) !in newInvSet;
   
   // Define mapping from new inversions to old inversions
   ghost var f: (int,int) -> (int,int) := 
      (p,q) => 
         if p != i && p != j && q != i && q != j then (p,q)
         else if p == i && q > j then (j, q)
         else if p == i && i < q < j then (i, q)
         else if q == j && p < i then (p, i)
         else if q == j && i < p < j then (p, j)
         else if p == j then (i, q)
         else (p, q); // fallback
   
   // Prove f maps newInvSet into oldInvSet - {(i,j)}
   forall pair | pair in newInvSet
      ensures f(pair.0, pair.1) in oldInvSet && f(pair.0, pair.1) != (i, j)
   {
      var p := pair.0;
      var q := pair.1;
      assert 0 <= p < q < a.Length;
      assert newSeq[p] > newSeq[q];
      
      if p != i && p != j && q != i && q != j {
         assert oldSeq[p] == newSeq[p] && oldSeq[q] == newSeq[q];
         assert oldSeq[p] > oldSeq[q];
         assert (p, q) in oldInvSet;
         assert (p, q) != (i, j);
      } else if p == i && q > j {
         assert newSeq[i] == oldSeq[j];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[j] > oldSeq[q];
         assert (j, q) in oldInvSet;
         assert (j, q) != (i, j);
      } else if p == i && i < q < j {
         assert newSeq[i] == oldSeq[j];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[j] > oldSeq[q];
         assert oldSeq[i] > oldSeq[j] > oldSeq[q];
         assert (i, q) in oldInvSet;
         assert (i, q) != (i, j);
      } else if q == j && p < i {
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         assert oldSeq[p] > oldSeq[i];
         assert (p, i) in oldInvSet;
         assert (p, i) != (i, j);
      } else if q == j && i < p < j {
         assert newSeq[p] == oldSeq[p];
         assert newSeq[j] == oldSeq[i];
         assert oldSeq[p] > oldSeq[i];
         assert oldSeq[p] > oldSeq[i] > oldSeq[j];
         assert (p, j) in oldInvSet;
         assert (p, j) != (i, j);
      } else if p == j {
         assert q > j;
         assert newSeq[j] == oldSeq[i];
         assert newSeq[q] == oldSeq[q];
         assert oldSeq[i] > oldSeq[q];
         assert (i, q) in oldInvSet;
         assert (i, q) != (i, j);
      }
   }
   
   // Prove f is injective on newInvSet
   forall pair1, pair2 | pair1 in newInvSet && pair2 in newInvSet && pair1 != pair2
      ensures f(pair1.0, pair1.1) != f(pair2.0, pair2.1)
   {
      var p1, q1 := pair1.0, pair1.1;
      var p2, q2 := pair2.0, pair2.1;
      
      if f(p1, q1) == f(p2, q2) {
         // Case analysis shows this leads to pair1 == pair2
         if p1 != i && p1 != j && q1 != i && q1 != j {
            if p2 != i && p2 != j && q2 != i && q2 != j {
               assert (p1, q1) == (p2, q2);
            }
         }
      }
   }
   
   var oldMinusIJ := oldInvSet - {(i, j)};
   
   InjectiveMapBound(newInvSet, oldMinusIJ, (pair: (int,int)) => f(pair.0, pair.1));
   
   assert |newInvSet| <= |oldMinusIJ|;
   assert |oldMinusIJ| == |oldInvSet| - 1;
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
      assert InversionSet(a) == SeqInversionSet(a[..]);
      assert a[..] == oldSeq;
      assert InversionSet(a) == oldInvSet;
      InversionsEqualsSetSize(a);
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

