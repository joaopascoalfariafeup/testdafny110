
// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper function to merge two sorted sequences - processes from front to match algorithm
ghost function {:fuel 10} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then [a[0]] + MergeSeq(a[1..], b)
    else [b[0]] + MergeSeq(a, b[1..])
}

// Helper predicate: all elements in s1 are <= all elements in s2
ghost predicate AllLessOrEqual(s1: seq<int>, s2: seq<int>)
{
    forall i, j :: 0 <= i < |s1| && 0 <= j < |s2| ==> s1[i] <= s2[j]
}

// Lemma about MergeSeq preserving multisets
lemma MergeSeqMultiset(a: seq<int>, b: seq<int>)
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqMultiset(a[1..], b);
    } else {
        MergeSeqMultiset(a, b[1..]);
    }
}

// Lemma: extending the first sequence when its first element is smaller
lemma MergeSeqExtendFirst(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a + [x])
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    requires |a| == 0 || a[|a|-1] <= x
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
{
    if |a| == 0 {
        if |b| == 0 {
        } else {
            assert a + [x] == [x];
        }
    } else if |b| == 0 {
        assert MergeSeq(a, b) == a;
        assert MergeSeq(a + [x], b) == a + [x];
    } else {
        assert a[0] <= x <= b[0];
        assert (a + [x])[0] == a[0];
        assert (a + [x])[1..] == a[1..] + [x];
        MergeSeqExtendFirst(a[1..], b, x);
    }
}

// Lemma: extending the second sequence when its first element is smaller
lemma MergeSeqExtendSecond(a: seq<int>, b: seq<int>, y: int)
    requires Sorted(a)
    requires Sorted(b + [y])
    requires |a| == 0 || a[0] > y
    requires |a| > 0 ==> y < a[0]
    requires |b| == 0 || b[|b|-1] <= y
    ensures MergeSeq(a, b + [y]) == MergeSeq(a, b) + [y]
{
    if |b| == 0 {
        if |a| == 0 {
        } else {
            assert b + [y] == [y];
            assert y < a[0];
        }
    } else if |a| == 0 {
        assert MergeSeq(a, b) == b;
        assert MergeSeq(a, b + [y]) == b + [y];
    } else {
        assert b[0] <= y < a[0];
        assert (b + [y])[0] == b[0];
        assert (b + [y])[1..] == b[1..] + [y];
        MergeSeqExtendSecond(a, b[1..], y);
    }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
// This routine is part of the merge sort algorithm. 
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires Sorted(a[..])
    requires Sorted(b[..])
    ensures c.Length == a.Length + b.Length
    ensures Sorted(c[..])
    ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
    ensures c[..] == MergeSeq(a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    // Repeatidly pick the smallest element from 'a' and 'b' and copy it into 'c'
    while i < a.Length || j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant i + j <= c.Length
        invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        invariant Sorted(c[..i+j])
        invariant i < a.Length ==> forall m :: 0 <= m < i + j ==> c[m] <= a[i]
        invariant j < b.Length ==> forall m :: 0 <= m < i + j ==> c[m] <= b[j]
        decreases a.Length - i + b.Length - j
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            c[j + i] := a[i];
            assert c[..i+j+1] == c[..i+j] + [a[i]];
            MergeSeqExtendFirst(a[..i], b[..j], a[i]);
            i := i + 1;
        } 
        else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            MergeSeqExtendSecond(a[..i], b[..j], b[j]);
            j := j + 1;
        }
    }
    assert i == a.Length && j == b.Length;
    assert a[..i] == a[..];
    assert b[..j] == b[..];
    assert c[..i+j] == c[..];
    MergeSeqMultiset(a[..], b[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert a[..] == [1, 3, 5];
    assert b[..] == [2, 4];
    assert c[..] == [1, 2, 3, 4, 5];
}



