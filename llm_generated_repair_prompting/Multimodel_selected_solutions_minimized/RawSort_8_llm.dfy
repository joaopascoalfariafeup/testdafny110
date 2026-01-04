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
      InjectiveMapBound(s', t', f);
   }
}

ghost function MapNewToOld(pair: (int, int), i: int, j: int, oldSeq: seq<T>, newSeq: seq<T>): (int, int)
{
   var p := pair.0;
   var q := pair.1;
   if p == i && q > j then (j, q)
   else if q == j && p < i then (p, i)
   else if p == j then (i, q)
   else if q == i then (p, j)
   else pair
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
   
   var oldMinusIJ := oldInvSet - {(i, j)};
   
   var mapF := (pair: (int, int)) => MapNewToOld(pair, i, j, oldSeq, newSeq);
   
   InjectiveMapBound(newInvSet, oldMinusIJ, mapF);
}

// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures Sorted(a[..])
   ensures Multiset(a[..]) == Multiset(old(a[..]))
   decreases Inversions(a)
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var oldSeq := a[..];
      ghost var oldInvSet := SeqInversionSet(oldSeq);
      assert InversionSet(a) == oldInvSet;
      a[i], a[j] := a[j], a[i]; // swap
      SwapDecreasesInversions(a, i, j, oldSeq);
      RawSort(a); // proceed recursivelly
   }
}



method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   ghost var oldSeq := a[..];
   assert oldSeq == [3, 5, 1];
   RawSort(a);
   assert a[..] == [1, 3, 5];
}