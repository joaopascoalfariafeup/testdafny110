
// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper function to merge two sorted sequences
ghost function {:fuel 10} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[|a|-1] >= b[|b|-1] then MergeSeq(a[..|a|-1], b) + [a[|a|-1]]
    else MergeSeq(a, b[..|b|-1]) + [b[|b|-1]]
}

// Lemma about MergeSeq preserving multisets
lemma MergeSeqMultiset(a: seq<int>, b: seq<int>)
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[|a|-1] >= b[|b|-1] {
        MergeSeqMultiset(a[..|a|-1], b);
        assert a == a[..|a|-1] + [a[|a|-1]];
    } else {
        MergeSeqMultiset(a, b[..|b|-1]);
        assert b == b[..|b|-1] + [b[|b|-1]];
    }
}

// Lemma: extending the first sequence when its last element is largest
lemma MergeSeqExtendFirst(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a)
    requires Sorted(b)
    requires |a| == 0 || a[|a|-1] <= x
    requires |b| == 0 || x >= b[|b|-1]
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |b| == 0 {
    } else if |a| == 0 {
    } else {
        assert (a + [x])[..|a|] == a;
    }
}

// Lemma: extending the second sequence when its last element is largest
lemma MergeSeqExtendSecond(a: seq<int>, b: seq<int>, y: int)
    requires Sorted(a)
    requires Sorted(b)
    requires |b| == 0 || b[|b|-1] <= y
    requires |a| == 0 || y > a[|a|-1]
    ensures MergeSeq(a, b + [y]) == MergeSeq(a, b) + [y]
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else {
        assert (b + [y])[..|b|] == b;
    }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires Sorted(a[..])
    requires Sorted(b[..])
    ensures c.Length == a.Length + b.Length
    ensures Sorted(c[..])
    ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
    ensures c[..] == MergeSeq(a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0;

    while i < a.Length || j < b.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= j <= b.Length
        invariant i + j <= c.Length
        invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        invariant Sorted(c[..i+j])
        invariant i + j > 0 && i < a.Length ==> c[i+j-1] <= a[i]
        invariant i + j > 0 && j < b.Length ==> c[i+j-1] <= b[j]
        decreases a.Length - i + b.Length - j
    {
        if i < a.Length && (j == b.Length || a[i] <= b[j]) {
            assert a[..i+1] == a[..i] + [a[i]];
            c[j + i] := a[i];
            assert c[..i+j+1] == c[..i+j] + [a[i]];
            MergeSeqExtendFirst(a[..i], b[..j], a[i]);
            i := i + 1;
        } else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            MergeSeqExtendSecond(a[..i], b[..j], b[j]);
            j := j + 1;
        }
    }
    assert a[..i] == a[..];
    assert b[..j] == b[..];
    assert c[..i+j] == c[..];
}

method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert a[..] == [1, 3, 5];
    assert b[..] == [2, 4];
    assert c[..] == [1, 2, 3, 4, 5];
}
