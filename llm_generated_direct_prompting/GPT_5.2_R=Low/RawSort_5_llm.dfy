/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 */

// Type of each array element; can be any type supporting comparision operators.
type T = int 


predicate SortedSeq(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate SortedArr(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

lemma NotExistsOutOfOrderImpliesSortedArr(a: array<T>)
  requires !(exists i, j :: 0 <= i < j < a.Length && a[i] > a[j])
  ensures SortedArr(a)
{
  assert forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
}

lemma MultisetInSeq<U>(s: seq<U>, x: U)
  requires x in multiset(s)
  ensures exists k :: 0 <= k < |s| && s[k] == x
  decreases |s|
{
  if |s| == 0 {
  } else {
    if s[0] == x {
    } else {
      assert x in multiset(s[1..]);
      MultisetInSeq(s[1..], x);
      var k :| 0 <= k < |s[1..]| && s[1..][k] == x;
      assert 0 <= k + 1 < |s|;
      assert s[k + 1] == x;
    }
  }
}

lemma SortedMultisetIs135(s: seq<int>)
  requires |s| == 3
  requires SortedSeq(s)
  requires multiset(s) == multiset([1, 3, 5])
  ensures s == [1, 3, 5]
{
  assert 1 in multiset(s);
  MultisetInSeq(s, 1);
  var k1 :| 0 <= k1 < |s| && s[k1] == 1;

  if s[0] != 1 {
    assert s[0] in multiset(s);
    assert s[0] in multiset([1, 3, 5]);
    assert s[0] == 3 || s[0] == 5;
    assert 0 < k1;
    assert s[0] <= s[k1];
    assert s[0] <= 1;
    assert false;
  }
  assert s[0] == 1;

  var t := s[1..];
  assert |t| == 2;
  assert multiset(t) == multiset([3, 5]);

  assert 3 in multiset(t);
  MultisetInSeq(t, 3);
  var k3 :| 0 <= k3 < |t| && t[k3] == 3;

  if t[0] != 3 {
    assert t[0] in multiset(t);
    assert t[0] in multiset([3, 5]);
    assert t[0] == 5;
    assert 0 < k3;
    assert t[0] <= t[k3];
    assert t[0] <= 3;
    assert false;
  }
  assert t[0] == 3;

  assert t[1] in multiset(t);
  assert t[1] in multiset([3, 5]);
  assert t[1] != 3;
  assert t[1] == 5;

  assert s == [1, 3, 5];
}


// Sorts an array by simply swapping elements out of order, chosen randomly.
method RawSort(a: array<T>)
   modifies a
   ensures SortedArr(a)
   ensures multiset(a[..]) == multiset(old(a[..]))
   decreases *
{
   if i, j :| 0 <= i < j < a.Length && a[i] > a[j]  {
      ghost var before := a[..];
      a[i], a[j] := a[j], a[i]; // swap
      assert multiset(a[..]) == multiset(before);
      RawSort(a); // proceed recursivelly
      assert multiset(a[..]) == multiset(before);
   } else {
      NotExistsOutOfOrderImpliesSortedArr(a);
   }
}


method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   RawSort(a);
   SortedMultisetIs135(a[..]);
   assert a[..] == [1, 3, 5];
}
