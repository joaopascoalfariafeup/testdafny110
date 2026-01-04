// Helper predicate to check if a sequence is sorted
ghost predicate Sorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if all elements in s1 are <= all elements in s2
ghost predicate AllLessOrEqual(s1: seq<int>, s2: seq<int>)
{
    forall i, j :: 0 <= i < |s1| && 0 <= j < |s2| ==> s1[i] <= s2[j]
}

// Lemma: prepending smallest element to sorted sequence keeps it sorted
lemma PrependSorted(x: int, s: seq<int>)
    requires Sorted(s)
    requires forall i :: 0 <= i < |s| ==> x <= s[i]
    ensures Sorted([x] + s)
{
}

// Helper function to merge two sorted sequences
ghost function {:fuel 6} MergeSeq(a: seq<int>, b: seq<int>): seq<int>
    requires Sorted(a) && Sorted(b)
    decreases |a| + |b|
    ensures |MergeSeq(a, b)| == |a| + |b|
    ensures Sorted(MergeSeq(a, b))
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then 
        var rest := MergeSeq(a[1..], b);
        PrependSorted(a[0], rest);
        [a[0]] + rest
    else 
        var rest := MergeSeq(a, b[1..]);
        PrependSorted(b[0], rest);
        [b[0]] + rest
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
    requires |b| > 0 && |a| > 0 && b[0] < a[0]
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
