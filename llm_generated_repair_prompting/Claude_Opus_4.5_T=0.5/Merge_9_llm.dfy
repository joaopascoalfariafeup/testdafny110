// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper function to merge two sorted sequences - processes from beginning
ghost function {:fuel 10} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then [a[0]] + MergeSeq(a[1..], b)
    else [b[0]] + MergeSeq(a, b[1..])
}

// Lemma about MergeSeq preserving multisets
lemma MergeSeqMultiset(a: seq<int>, b: seq<int>)
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqMultiset(a[1..], b);
        assert a == [a[0]] + a[1..];
    } else {
        MergeSeqMultiset(a, b[1..]);
        assert b == [b[0]] + b[1..];
    }
}

// Lemma: MergeSeq produces sorted output
lemma MergeSeqSorted(a: seq<int>, b: seq<int>)
    requires Sorted(a)
    requires Sorted(b)
    ensures Sorted(MergeSeq(a, b))
    decreases |a| + |b|
{
    if |a| == 0 || |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqSorted(a[1..], b);
    } else {
        MergeSeqSorted(a, b[1..]);
    }
}

// Lemma: prepending to first sequence
lemma MergeSeqPrependFirst(x: int, a: seq<int>, b: seq<int>)
    requires Sorted([x] + a)
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    ensures MergeSeq([x] + a, b) == [x] + MergeSeq(a, b)
{
    assert ([x] + a)[0] == x;
    assert ([x] + a)[1..] == a;
}

// Lemma: prepending to second sequence
lemma MergeSeqPrependSecond(a: seq<int>, x: int, b: seq<int>)
    requires Sorted(a)
    requires Sorted([x] + b)
    requires |a| == 0 || x < a[0]
    ensures MergeSeq(a, [x] + b) == [x] + MergeSeq(a, b)
{
    if |a| == 0 {
    } else {
        assert ([x] + b)[0] == x;
        assert ([x] + b)[1..] == b;
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
        invariant c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..])
        invariant Sorted(c[..i+j])
        invariant i + j > 0 && i < a.Length ==> c[i+j-1] <= a[i]
        invariant i + j > 0 && j < b.Length ==> c[i+j-1] <= b[j]
        decreases a.Length - i + b.Length - j
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            c[j + i] := a[i];
            assert c[..i+j+1] == c[..i+j] + [a[i]];
            
            // Key: a[i..] == [a[i]] + a[i+1..]
            assert a[i..] == [a[i]] + a[i+1..];
            MergeSeqPrependFirst(a[i], a[i+1..], b[j..]);
            
            i := i + 1;
        } 
        else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            assert i < a.Length ==> b[j] < a[i];
            
            // Key: b[j..] == [b[j]] + b[j+1..]
            assert b[j..] == [b[j]] + b[j+1..];
            MergeSeqPrependSecond(a[i..], b[j], b[j+1..]);
            
            j := j + 1;
        }
    }
    assert i == a.Length && j == b.Length;
    assert a[i..] == [];
    assert b[j..] == [];
    assert MergeSeq(a[i..], b[j..]) == [];
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
