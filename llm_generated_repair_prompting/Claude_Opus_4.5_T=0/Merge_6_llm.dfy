// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper function to merge two sorted sequences
ghost function {:fuel 6} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
    requires Sorted(a) && Sorted(b)
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then 
        [a[0]] + MergeSeq(a[1..], b)
    else 
        [b[0]] + MergeSeq(a, b[1..])
}

lemma MergeSeqProperties(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures |MergeSeq(a, b)| == |a| + |b|
    ensures Sorted(MergeSeq(a, b))
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqProperties(a[1..], b);
    } else {
        MergeSeqProperties(a, b[1..]);
    }
}

// Lemma: when a is empty, MergeSeq(a, b) == b
lemma MergeSeqEmptyA(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |a| == 0
    ensures MergeSeq(a, b) == b
{
}

// Lemma: when b is empty, MergeSeq(a, b) == a
lemma MergeSeqEmptyB(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |b| == 0
    ensures MergeSeq(a, b) == a
{
}

// Lemma: when a[0] <= b[0], MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b)
lemma MergeSeqTakeA(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |a| > 0 && (|b| == 0 || a[0] <= b[0])
    ensures MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b)
{
}

// Lemma: when b[0] < a[0], MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..])
lemma MergeSeqTakeB(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |b| > 0 && (|a| == 0 || b[0] < a[0])
    ensures MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..])
{
}

// Lemma to connect slices with full arrays
lemma MergeSeqSlice(a: seq<int>, b: seq<int>, i: int, j: int)
    requires Sorted(a) && Sorted(b)
    requires 0 <= i <= |a| && 0 <= j <= |b|
    ensures Sorted(a[i..]) && Sorted(b[j..])
    ensures Sorted(a[..i]) && Sorted(b[..j])
{
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
        invariant Sorted(a[i..]) && Sorted(b[j..])
        invariant Sorted(a[..i]) && Sorted(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        decreases a.Length - i + b.Length - j
    {
        MergeSeqSlice(a[..], b[..], i, j);
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            MergeSeqTakeA(a[i..], b[j..]);
            assert MergeSeq(a[i..], b[j..]) == [a[i]] + MergeSeq(a[i+1..], b[j..]);
            c[j + i] := a[i];
            i := i + 1;
        } 
        else {
            assert j < b.Length;
            assert b[..j+1] == b[..j] + [b[j]];
            MergeSeqTakeB(a[i..], b[j..]);
            assert MergeSeq(a[i..], b[j..]) == [b[j]] + MergeSeq(a[i..], b[j+1..]);
            c[i + j] := b[j];
            j := j + 1;
        }
    }
    assert a[..] == a[..a.Length];
    assert b[..] == b[..b.Length];
    assert c[..] == c[..c.Length];
    MergeSeqProperties(a[..], b[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    assert a[..] == [1, 3, 5];
    assert b[..] == [2, 4];
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

