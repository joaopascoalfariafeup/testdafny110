
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 50} MergeSeq(sa: seq<int>, sb: seq<int>): seq<int>
  decreases |sa| + |sb|
{
  if |sa| == 0 then sb
  else if |sb| == 0 then sa
  else if sa[0] <= sb[0] then [sa[0]] + MergeSeq(sa[1..], sb)
  else [sb[0]] + MergeSeq(sa, sb[1..])
}

lemma SortedHeadLeAll(s: seq<int>)
  requires Sorted(s)
  requires |s| > 0
  ensures forall k :: 0 <= k < |s| ==> s[0] <= s[k]
{
  forall k | 0 <= k < |s| ensures s[0] <= s[k] {
    if k == 0 {
    } else {
      assert 0 <= 0 < k < |s|;
    }
  }
}

lemma SortedPrepend(x: int, t: seq<int>)
  requires Sorted(t)
  requires forall k :: 0 <= k < |t| ==> x <= t[k]
  ensures Sorted([x] + t)
{
  forall i, j | 0 <= i < j < |[x] + t|
    ensures ([x] + t)[i] <= ([x] + t)[j]
  {
    if i == 0 {
      // then j >= 1, so ([x]+t)[j] is t[j-1]
      assert 0 <= j - 1 < |t|;
    } else {
      // both indices land in t
      assert 0 <= i - 1 < j - 1 < |t|;
    }
  }
}

lemma MergeSeqMembership(sa: seq<int>, sb: seq<int>, x: int)
  ensures x in MergeSeq(sa, sb) <==> x in sa || x in sb
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    MergeSeqMembership(sa[1..], sb, x);
    assert MergeSeq(sa, sb) == [sa[0]] + MergeSeq(sa[1..], sb);
  } else {
    MergeSeqMembership(sa, sb[1..], x);
    assert MergeSeq(sa, sb) == [sb[0]] + MergeSeq(sa, sb[1..]);
  }
}

lemma MergeSeqMultiset(sa: seq<int>, sb: seq<int>)
  ensures multiset(MergeSeq(sa, sb)) == multiset(sa) + multiset(sb)
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    assert |sa| > 0;
    MergeSeqMultiset(sa[1..], sb);

    assert MergeSeq(sa, sb) == [sa[0]] + MergeSeq(sa[1..], sb);
    assert sa == [sa[0]] + sa[1..];

    assert multiset(MergeSeq(sa, sb)) == multiset([sa[0]]) + multiset(MergeSeq(sa[1..], sb));
    assert multiset(sa) == multiset([sa[0]]) + multiset(sa[1..]);
  } else {
    assert |sb| > 0;
    MergeSeqMultiset(sa, sb[1..]);

    assert MergeSeq(sa, sb) == [sb[0]] + MergeSeq(sa, sb[1..]);
    assert sb == [sb[0]] + sb[1..];

    assert multiset(MergeSeq(sa, sb)) == multiset([sb[0]]) + multiset(MergeSeq(sa, sb[1..]));
    assert multiset(sb) == multiset([sb[0]]) + multiset(sb[1..]);
  }
}

lemma MergeSeqSorted(sa: seq<int>, sb: seq<int>)
  requires Sorted(sa) && Sorted(sb)
  ensures Sorted(MergeSeq(sa, sb))
  decreases |sa| + |sb|
{
  if |sa| == 0 {
  } else if |sb| == 0 {
  } else if sa[0] <= sb[0] {
    MergeSeqSorted(sa[1..], sb);

    SortedHeadLeAll(sa);
    SortedHeadLeAll(sb);

    forall k | 0 <= k < |MergeSeq(sa[1..], sb)|
      ensures sa[0] <= MergeSeq(sa[1..], sb)[k]
    {
      var x := MergeSeq(sa[1..], sb)[k];
      MergeSeqMembership(sa[1..], sb, x);
      if x in sa[1..] {
        var t :| 0 <= t < |sa[1..]| && sa[1..][t] == x;
        assert sa[1..][t] == sa[t+1];
        assert 0 <= t+1 < |sa|;
        assert sa[0] <= sa[t+1];
        assert sa[0] <= x;
      } else {
        var t :| 0 <= t < |sb| && sb[t] == x;
        assert sb[0] <= sb[t];
        assert sa[0] <= sb[0];
        assert sa[0] <= x;
      }
    }

    SortedPrepend(sa[0], MergeSeq(sa[1..], sb));
    assert MergeSeq(sa, sb) == [sa[0]] + MergeSeq(sa[1..], sb);
  } else {
    MergeSeqSorted(sa, sb[1..]);

    SortedHeadLeAll(sa);
    SortedHeadLeAll(sb);

    forall k | 0 <= k < |MergeSeq(sa, sb[1..])|
      ensures sb[0] <= MergeSeq(sa, sb[1..])[k]
    {
      var x := MergeSeq(sa, sb[1..])[k];
      MergeSeqMembership(sa, sb[1..], x);
      if x in sb[1..] {
        var t :| 0 <= t < |sb[1..]| && sb[1..][t] == x;
        assert sb[1..][t] == sb[t+1];
        assert 0 <= t+1 < |sb|;
        assert sb[0] <= sb[t+1];
        assert sb[0] <= x;
      } else {
        var t :| 0 <= t < |sa| && sa[t] == x;
        assert sa[0] <= sa[t];
        assert sb[0] <= sa[0]; // since we are in the else-branch of sa[0] <= sb[0]
        assert sb[0] <= x;
      }
    }

    SortedPrepend(sb[0], MergeSeq(sa, sb[1..]));
    assert MergeSeq(sa, sb) == [sb[0]] + MergeSeq(sa, sb[1..]);
  }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c.Length == a.Length + b.Length
  ensures c[..] == MergeSeq(a[..], b[..])
  ensures Sorted(c[..])
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0;

    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..])
      decreases c.Length - (i + j)
    {
        assert i + j < c.Length;
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            assert a[i..] != [];
            assert MergeSeq(a[i..], b[j..]) == [a[i]] + MergeSeq(a[i+1..], b[j..]);
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            assert b[j..] != [];
            assert MergeSeq(a[i..], b[j..]) == [b[j]] + MergeSeq(a[i..], b[j+1..]);
            j := j + 1;
        }
    }

    assert i == a.Length && j == b.Length;
    assert a[i..] == [];
    assert b[j..] == [];
    assert MergeSeq(a[i..], b[j..]) == [];
    assert c[..i+j] == c[..];
    assert c[..] + MergeSeq(a[i..], b[j..]) == c[..];
    assert c[..] == MergeSeq(a[..], b[..]);

    MergeSeqSorted(a[..], b[..]);
    MergeSeqMultiset(a[..], b[..]);
    assert Sorted(MergeSeq(a[..], b[..]));
    assert Sorted(c[..]);
    assert multiset(c[..]) == multiset(MergeSeq(a[..], b[..]));
}

lemma MergeSeq_Example_135_24()
  ensures MergeSeq([1,3,5], [2,4]) == [1,2,3,4,5]
{
  calc {
    MergeSeq([1,3,5], [2,4]);
    == { }
    [1] + MergeSeq([3,5], [2,4]);
    == { }
    [1] + ([2] + MergeSeq([3,5], [4]));
    == { }
    [1,2] + MergeSeq([3,5], [4]);
    == { }
    [1,2] + ([3] + MergeSeq([5], [4]));
    == { }
    [1,2,3] + MergeSeq([5], [4]);
    == { }
    [1,2,3] + ([4] + MergeSeq([5], []));
    == { }
    [1,2,3,4] + MergeSeq([5], []);
    == { }
    [1,2,3,4] + [5];
    == { }
    [1,2,3,4,5];
  }
}

method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);

    assert a[..] == [1,3,5];
    assert b[..] == [2,4];
    MergeSeq_Example_135_24();
    assert MergeSeq(a[..], b[..]) == [1,2,3,4,5];

    assert c[..] == [1, 2, 3, 4, 5];
}

