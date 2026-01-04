/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 

predicate SortedArray(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

function Count(s: seq<T>, x: T): int
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], x) + (if s[|s|-1] == x then 1 else 0)
}

lemma CountUpdate(s: seq<T>, idx: int, v: T, x: T)
  requires 0 <= idx < |s|
  ensures Count(s[idx := v], x) == Count(s, x) + (if v == x then 1 else 0) - (if s[idx] == x then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
    // impossible by precondition
  } else if idx == |s|-1 {
    // Update affects the last element only
    assert (s[idx := v])[..|s|-1] == s[..|s|-1];
    assert (s[idx := v])[|s|-1] == v;
    // Unfold Count on both sides
    assert Count(s[idx := v], x) == Count((s[idx := v])[..|s|-1], x) + (if (s[idx := v])[|s|-1] == x then 1 else 0);
    assert Count(s, x) == Count(s[..|s|-1], x) + (if s[|s|-1] == x then 1 else 0);
    assert s[idx] == s[|s|-1];
  } else {
    // idx < last, so last element unchanged; recurse on the prefix
    assert idx < |s|-1;
    assert (s[idx := v])[|s|-1] == s[|s|-1];
    assert (s[idx := v])[..|s|-1] == (s[..|s|-1])[idx := v];

    CountUpdate(s[..|s|-1], idx, v, x);

    // Unfold Count for s and s[idx:=v]
    assert Count(s[idx := v], x) == Count((s[idx := v])[..|s|-1], x) + (if (s[idx := v])[|s|-1] == x then 1 else 0);
    assert Count(s, x) == Count(s[..|s|-1], x) + (if s[|s|-1] == x then 1 else 0);

    // Replace with established equalities about prefix and last
    assert Count((s[idx := v])[..|s|-1], x) == Count((s[..|s|-1])[idx := v], x);
    assert (if (s[idx := v])[|s|-1] == x then 1 else 0) == (if s[|s|-1] == x then 1 else 0);
  }
}

lemma CountSwapPreserved(s: seq<T>, i: int, j: int, x: T)
  requires 0 <= i < j < |s|
  ensures Count(s[i := s[j]][j := s[i]], x) == Count(s, x)
{
  CountUpdate(s, i, s[j], x);
  var s1 := s[i := s[j]];
  assert s1[j] == s[j];
  CountUpdate(s1, j, s[i], x);
  assert s1[i] == s[j];

  if s[i] == x {
    if s[j] == x {
    } else {
    }
  } else {
    if s[j] == x {
    } else {
    }
  }
}

// --- Termination metric: inversion count ---

function InversionPairs(s: seq<T>): set<(int,int)>
{
  set p, q | 0 <= p < q < |s| && s[p] > s[q] :: (p, q)
}

function InversionCount(s: seq<T>): nat
{
  |InversionPairs(s)|
}

// --- Proof helpers for inversion decrease under swapping an inverted pair ---

function Sigma(i: int, j: int, k: int): int
{
  if k == i then j else if k == j then i else k
}

lemma SigmaInvolutive(i: int, j: int, k: int)
  ensures Sigma(i, j, Sigma(i, j, k)) == k
{
  if k == i {
  } else if k == j {
  } else {
  }
}

function MapPair(i: int, j: int, pq: (int,int)): (int,int)
  requires pq.0 < pq.1
{
  var p := Sigma(i, j, pq.0);
  var q := Sigma(i, j, pq.1);
  if p < q then (p, q) else (q, p)
}

lemma MapPairInvolutive(i: int, j: int, pq: (int,int))
  requires pq.0 < pq.1
  ensures MapPair(i, j, MapPair(i, j, pq)) == pq
{
  var p1 := Sigma(i, j, pq.0);
  var q1 := Sigma(i, j, pq.1);

  if p1 < q1 {
    // First map is (p1,q1)
    assert MapPair(i, j, pq) == (p1, q1);
    SigmaInvolutive(i, j, pq.0);
    SigmaInvolutive(i, j, pq.1);
    assert Sigma(i, j, p1) == pq.0;
    assert Sigma(i, j, q1) == pq.1;
    // Second map is (pq.0,pq.1) (already ordered by precondition)
    assert MapPair(i, j, (p1, q1)) == pq;
  } else {
    // First map is (q1,p1)
    assert MapPair(i, j, pq) == (q1, p1);
    SigmaInvolutive(i, j, pq.0);
    SigmaInvolutive(i, j, pq.1);
    assert Sigma(i, j, q1) == pq.1;
    assert Sigma(i, j, p1) == pq.0;
    // Second map of (q1,p1) is canonicalization of (pq.1,pq.0) which is pq
    assert MapPair(i, j, (q1, p1)) == pq;
  }
}

lemma MapPairInjective(i: int, j: int, A: set<(int,int)>)
  requires forall pq :: pq in A ==> pq.0 < pq.1
  ensures forall pq1, pq2 :: pq1 in A && pq2 in A && pq1 != pq2 ==> MapPair(i, j, pq1) != MapPair(i, j, pq2)
{
  forall pq1, pq2 | pq1 in A && pq2 in A && pq1 != pq2
    ensures MapPair(i, j, pq1) != MapPair(i, j, pq2)
  {
    if MapPair(i, j, pq1) == MapPair(i, j, pq2) {
      MapPairInvolutive(i, j, pq1);
      MapPairInvolutive(i, j, pq2);
      assert MapPair(i, j, MapPair(i, j, pq1)) == MapPair(i, j, MapPair(i, j, pq2));
      assert pq1 == pq2;
      assert false;
    }
  }
}

lemma CardLeqByInjection<A,B>(Aset: set<A>, Bset: set<B>, f: A -> B)
  requires Aset.Finite && Bset.Finite
  requires forall a :: a in Aset ==> f(a) in Bset
  requires forall a1, a2 :: a1 in Aset && a2 in Aset && a1 != a2 ==> f(a1) != f(a2)
  ensures |Aset| <= |Bset|
  decreases |Aset|
{
  if |Aset| == 0 {
  } else {
    var a :| a in Aset;
    var A1 := Aset - {a};
    var b := f(a);
    var B1 := Bset - {b};

    assert a in Aset;
    assert b in Bset;

    assert forall x :: x in A1 ==> f(x) in B1 by {
      forall x | x in A1
        ensures f(x) in B1
      {
        assert x in Aset;
        assert f(x) in Bset;
        if f(x) == b {
          assert f(x) == f(a);
          assert x == a;
          assert x !in A1;
        }
      }
    }

    assert forall x1, x2 :: x1 in A1 && x2 in A1 && x1 != x2 ==> f(x1) != f(x2) by {
      forall x1, x2 | x1 in A1 && x2 in A1 && x1 != x2
        ensures f(x1) != f(x2)
      {
        assert x1 in Aset && x2 in Aset;
      }
    }

    CardLeqByInjection(A1, B1, f);

    assert |Aset| == |A1| + 1;
    assert |Bset| == |B1| + 1;
  }
}

lemma SwapDecreasesInversions(s: seq<T>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] > s[j]
  ensures InversionCount(s[i := s[j]][j := s[i]]) < InversionCount(s)
{
  var t := s[i := s[j]][j := s[i]];
  var S := InversionPairs(s);
  var T := InversionPairs(t);

  // (i,j) is in S
  assert (i, j) in S;

  // (i,j) is not in T
  assert (i, j) !in T by {
    assert t[i] == s[j];
    assert t[j] == s[i];
    assert !(t[i] > t[j]);
  }

  // Key relation: t[k] == s[Sigma(i,j,k)]
  assert forall k :: 0 <= k < |s| ==> t[k] == s[Sigma(i, j, k)] by {
    forall k
      ensures 0 <= k < |s| ==> t[k] == s[Sigma(i, j, k)]
    {
      if 0 <= k < |s| {
        if k == i {
          assert t[k] == s[j];
          assert Sigma(i, j, k) == j;
        } else if k == j {
          assert t[k] == s[i];
          assert Sigma(i, j, k) == i;
        } else {
          assert t[k] == s[k];
          assert Sigma(i, j, k) == k;
        }
      }
    }
  }

  // Show: MapPair maps every inversion of t into an inversion of s, and never to (i,j)
  var B := S - {(i, j)};
  assert forall pq :: pq in T ==> pq.0 < pq.1 by {
    forall pq
      ensures pq in T ==> pq.0 < pq.1
    {
      if pq in T {
        assert 0 <= pq.0 < pq.1 < |t|;
      }
    }
  }

  assert forall pq :: pq in T ==> MapPair(i, j, pq) in B by {
    forall pq
      ensures pq in T ==> MapPair(i, j, pq) in B
    {
      if pq in T {
        var p := pq.0;
        var q := pq.1;
        assert 0 <= p < q < |t|;
        assert t[p] > t[q];

        var p1 := Sigma(i, j, p);
        var q1 := Sigma(i, j, q);

        // Translate inversion back to s using the t[k]=s[Sigma(...)] relation
        assert t[p] == s[p1];
        assert t[q] == s[q1];
        assert s[p1] > s[q1];

        // Canonicalize to an ordered pair
        var mp := MapPair(i, j, pq);
        assert mp.0 < mp.1;

        if p1 < q1 {
          assert mp == (p1, q1);
          assert (p1, q1) in S;
        } else {
          assert mp == (q1, p1);
          assert (q1, p1) in S;
        }

        if mp == (i, j) {
          assert p1 == i || p1 == j;
          assert q1 == i || q1 == j;
          assert p == i && q == j;
          assert false;
        }

        assert mp in B;
      }
    }
  }

  // Injectivity of MapPair on T
  MapPairInjective(i, j, T);

  // Now |T| <= |B|, hence |T| <= |S|-1, hence strict decrease
  CardLeqByInjection(T, B, (pq: (int,int)) => MapPair(i, j, pq));
  assert |B| + 1 == |S|; // since (i,j) in S
  assert |T| < |S|;
}

// --- Sorting ---

method RawSortAux(a: array<T>, ghost s0: seq<T>, ghost k: nat)
   modifies a
   requires a != null
   requires k == InversionCount(a[..])
   requires forall x: T :: Count(a[..], x) == Count(s0, x)
   ensures SortedArray(a)
   ensures forall x: T :: Count(a[..], x) == Count(s0, x)
   decreases k
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var sb := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert a[..] == sb[i := sb[j]][j := sb[i]];

      // Termination: inversions strictly decrease
      assert InversionCount(a[..]) < InversionCount(sb) by {
        SwapDecreasesInversions(sb, i, j);
        assert a[..] == sb[i := sb[j]][j := sb[i]];
      }

      // Counts still match s0 after swap (needed for recursive-call precondition)
      assert forall x: T :: Count(a[..], x) == Count(s0, x) by {
        forall x: T
          ensures Count(a[..], x) == Count(s0, x)
        {
          CountSwapPreserved(sb, i, j, x);
          assert Count(a[..], x) == Count(sb, x);
        }
      }

      // Recurse with decreased measure
      RawSortAux(a, s0, InversionCount(a[..]));

      // Count preservation: sb had the same counts as s0 at entry; recursion ensures a[..] has the same counts as s0
      assert forall x: T :: Count(sb, x) == Count(a[..], x) by {
        forall x: T
          ensures Count(sb, x) == Count(a[..], x)
        {
          assert Count(sb, x) == Count(s0, x);
          assert Count(a[..], x) == Count(s0, x);
        }
      }
   } else {
      assert forall i0: int, j0: int :: 0 <= i0 < j0 < a.Length ==> a[i0] <= a[j0] by {
        forall i0: int, j0: int
          ensures 0 <= i0 < j0 < a.Length ==> a[i0] <= a[j0]
        {
          if 0 <= i0 < j0 < a.Length {
            if a[i0] > a[j0] {
              assert exists ii: int, jj: int :: 0 <= ii < jj < a.Length && a[ii] > a[jj] by {
                assert 0 <= i0 < j0 < a.Length && a[i0] > a[j0];
              }
              assert false;
            }
          }
        }
      }
      assert SortedArray(a);
   }
}

method RawSort(a: array<T>)
   modifies a
   requires a != null
   ensures SortedArray(a)
   ensures forall x: T :: Count(a[..], x) == Count(old(a[..]), x)
{
   ghost var s0 := a[..];
   assert forall x: T :: Count(a[..], x) == Count(s0, x);
   RawSortAux(a, s0, InversionCount(a[..]));
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   assert a[..] == [1, 3, 5];
}

