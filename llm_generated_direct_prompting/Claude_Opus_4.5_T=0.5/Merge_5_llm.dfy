
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

// Helper function to merge two sorted sequences
ghost function MergeSeq(a: seq<int>, b: seq<int>): seq<int>
    decreases |a| + |b|
{
    if |a| == 0 then b
    else if |b| == 0 then a
    else if a[0] <= b[0] then [a[0]] + MergeSeq(a[1..], b)
    else [b[0]] + MergeSeq(a, b[1..])
}

// Lemma: merging sorted sequences produces a sorted sequence
lemma MergeSeqSorted(a: seq<int>, b: seq<int>)
    requires Sorted(a)
    requires Sorted(b)
    ensures Sorted(MergeSeq(a, b))
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqSorted(a[1..], b);
        var rest := MergeSeq(a[1..], b);
        assert Sorted(rest);
        assert forall k :: 0 <= k < |rest| ==> a[0] <= rest[k] by {
            MergeSeqContents(a[1..], b);
        }
    } else {
        MergeSeqSorted(a, b[1..]);
        var rest := MergeSeq(a, b[1..]);
        assert Sorted(rest);
        assert forall k :: 0 <= k < |rest| ==> b[0] <= rest[k] by {
            MergeSeqContents(a, b[1..]);
        }
    }
}

// Lemma: MergeSeq contains exactly the elements from both sequences
lemma MergeSeqContents(a: seq<int>, b: seq<int>)
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    ensures |MergeSeq(a, b)| == |a| + |b|
    ensures forall x :: x in MergeSeq(a, b) <==> x in a || x in b
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqContents(a[1..], b);
    } else {
        MergeSeqContents(a, b[1..]);
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
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            c[j + i] := a[i];
            i := i + 1;
        } 
        else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            j := j + 1;
        }
    }
    assert a[..] == a[..a.Length];
    assert b[..] == b[..b.Length];
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

