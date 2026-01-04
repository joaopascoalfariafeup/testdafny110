/* 
* Formal verification with Dafny of the selection sort algorithm 
* described in https://en.wikipedia.org/wiki/Selection_sort  
*/

predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

lemma SeqSplitLast<T>(s: seq<T>)
  requires |s| > 0
  ensures s == s[..|s|-1] + [s[|s|-1]]
{
}

lemma SeqSplitHead<T>(s: seq<T>)
  requires |s| > 0
  ensures s == [s[0]] + s[1..]
{
}

lemma MultisetSplitLast(s: seq<int>)
  requires |s| > 0
  ensures multiset(s) == multiset(s[..|s|-1]) + multiset([s[|s|-1]])
{
  SeqSplitLast(s);
  calc {
    multiset(s);
    == { }
    multiset(s[..|s|-1] + [s[|s|-1]]);
    == { }
    multiset(s[..|s|-1]) + multiset([s[|s|-1]]);
  }
}

lemma MultisetSplitHead(s: seq<int>)
  requires |s| > 0
  ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
{
  SeqSplitHead(s);
  calc {
    multiset(s);
    == { }
    multiset([s[0]] + s[1..]);
    == { }
    multiset([s[0]]) + multiset(s[1..]);
  }
}

lemma MultisetMinusOfSum(m: multiset<int>, n: multiset<int>, p: multiset<int>)
  requires m == n + p
  ensures m - n == p
{
  // Prove extensional equality by showing equal counts for all values
  forall v:int
    ensures (m - n)[v] == p[v]
  {
    assert m[v] == (n + p)[v];
    assert (n + p)[v] == n[v] + p[v];
    assert m[v] == n[v] + p[v];

    // show subtraction does not underflow
    assert 0 <= p[v];
    assert n[v] <= m[v];

    // multiset subtraction is pointwise max(m[v]-n[v], 0)
    assert (m - n)[v] == if m[v] - n[v] < 0 then 0 else m[v] - n[v];
    assert m[v] - n[v] == p[v];
    assert (m - n)[v] == p[v];
  }
  assert m - n == p;
}

lemma MultisetTail(s: seq<int>)
  requires |s| > 0
  ensures multiset(s[1..]) == multiset(s) - multiset([s[0]])
{
  MultisetSplitHead(s);
  MultisetMinusOfSum(multiset(s), multiset([s[0]]), multiset(s[1..]));
}

lemma CountZeroIfAllNeq(s: seq<int>, v: int)
  requires forall k :: 0 <= k < |s| ==> s[k] != v
  ensures multiset(s)[v] == 0
{
  if |s| == 0 {
  } else {
    CountZeroIfAllNeq(s[..|s|-1], v);
    MultisetSplitLast(s);
    assert s[|s|-1] != v;
    assert multiset([s[|s|-1]])[v] == 0;
    assert multiset(s)[v] == multiset(s[..|s|-1])[v] + multiset([s[|s|-1]])[v];
  }
}

lemma InMultisetSeqImpliesExistsIndex(s: seq<int>, v: int)
  requires v in multiset(s)
  ensures exists i :: 0 <= i < |s| && s[i] == v
{
  if |s| == 0 {
  } else {
    if v in multiset(s[..|s|-1]) {
      InMultisetSeqImpliesExistsIndex(s[..|s|-1], v);
      var i :| 0 <= i < |s[..|s|-1]| && s[..|s|-1][i] == v;
      assert 0 <= i < |s| && s[i] == v;
    } else {
      MultisetSplitLast(s);
      assert v in multiset([s[|s|-1]]);
      assert s[|s|-1] == v;
      assert exists i :: 0 <= i < |s| && s[i] == v;
    }
  }
}

lemma {:induction t} SortedAndMultisetEqToStrictIncImpliesEq(s: seq<int>, t: seq<int>)
  requires Sorted(s)
  requires StrictlyIncreasing(t)
  requires multiset(s) == multiset(t)
  ensures s == t
{
  assert |multiset(s)| == |s|;
  assert |multiset(t)| == |t|;
  assert |s| == |t|;

  if |t| == 0 {
    assert |s| == 0;
  } else {
    assert t[0] in multiset(t);
    assert t[0] in multiset(s);
    InMultisetSeqImpliesExistsIndex(s, t[0]);
    var k: int :| 0 <= k < |s| && s[k] == t[0];
    assert 0 <= 0 < k + 1 <= |s|;
    assert s[0] <= s[k];
    assert s[0] <= t[0];

    if s[0] < t[0] {
      assert forall kk :: 0 <= kk < |t| ==> t[0] <= t[kk];
      assert forall kk :: 0 <= kk < |t| ==> s[0] != t[kk];
      CountZeroIfAllNeq(t, s[0]);
      assert multiset(t)[s[0]] == 0;
      assert s[0] in multiset(s);
      assert multiset(s)[s[0]] > 0;
      assert false;
    }
    assert s[0] == t[0];

    var s1 := s[1..];
    var t1 := t[1..];

    MultisetTail(s);
    MultisetTail(t);
    assert multiset(s1) == multiset(s) - multiset([s[0]]);
    assert multiset(t1) == multiset(t) - multiset([t[0]]);
    assert multiset(s1) == multiset(t1);

    assert Sorted(s1);
    assert StrictlyIncreasing(t1);

    SortedAndMultisetEqToStrictIncImpliesEq(s1, t1);

    assert s == [s[0]] + s1;
    assert t == [t[0]] + t1;
  }
}

// Sorts array 'a' using the selection sort algorithm.
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant Sorted(a[..i])
      invariant forall p, q :: 0 <= p < i && i <= q < a.Length ==> a[p] <= a[q]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
        var jMin := i;
        for j := i + 1 to a.Length
          invariant i + 1 <= j <= a.Length
          invariant i <= jMin < j
          invariant forall k :: i <= k < j ==> a[jMin] <= a[k]
          invariant multiset(a[..]) == old(multiset(a[..]))
          invariant Sorted(a[..i])
          invariant forall p, q :: 0 <= p < i && i <= q < a.Length ==> a[p] <= a[q]
        {
            if a[j] < a[jMin] {
                jMin := j;
            }
        } 
        if jMin != i {
          a[i], a[jMin] := a[jMin], a[i]; 
        }
    }
}

lemma MultisetExample_94618()
  ensures multiset([9, 4, 6, 1, 8]) == multiset([1, 4, 6, 8, 9])
{
  calc {
    multiset([9, 4, 6, 1, 8]);
    == { }
    multiset([9] + [4, 6, 1, 8]);
    == { }
    multiset([9]) + multiset([4, 6, 1, 8]);
    == { }
    multiset([9]) + (multiset([4]) + multiset([6, 1, 8]));
    == { }
    multiset([9]) + (multiset([4]) + (multiset([6]) + multiset([1, 8])));
    == { }
    multiset([9]) + (multiset([4]) + (multiset([6]) + (multiset([1]) + multiset([8]))));
    == { }
    multiset([1]) + multiset([4]) + multiset([6]) + multiset([8]) + multiset([9]);
    == { }
    multiset([1] + [4, 6, 8, 9]);
    == { }
    multiset([1, 4, 6, 8, 9]);
  }
}

// Test case checked statically.
method testSelectionSort() {
  var a := new int[] [9, 4, 6, 1, 8];
  var target := [1, 4, 6, 8, 9];
  assert StrictlyIncreasing(target);
  assert a[..] == [9, 4, 6, 1, 8];
  MultisetExample_94618();
  assert multiset(a[..]) == multiset(target);

  SelectionSort(a);

  SortedAndMultisetEqToStrictIncImpliesEq(a[..], target);
  assert a[..] == [1, 4, 6, 8, 9];
}
