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

lemma MergeSeqSorted(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures Sorted(MergeSeq(a, b))
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqSorted(a[1..], b);
        var rest := MergeSeq(a[1..], b);
        assert MergeSeq(a, b) == [a[0]] + rest;
        assert Sorted(rest);
        if |rest| > 0 {
            assert rest[0] == MergeSeq(a[1..], b)[0];
            MergeSeqFirstElement(a[1..], b);
        }
    } else {
        MergeSeqSorted(a, b[1..]);
        var rest := MergeSeq(a, b[1..]);
        assert MergeSeq(a, b) == [b[0]] + rest;
        if |rest| > 0 {
            MergeSeqFirstElement(a, b[1..]);
        }
    }
}

lemma MergeSeqFirstElement(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |a| > 0 || |b| > 0
    ensures |MergeSeq(a, b)| > 0
    ensures (|a| > 0 && (|b| == 0 || a[0] <= b[0])) ==> MergeSeq(a, b)[0] == a[0]
    ensures (|b| > 0 && (|a| == 0 || b[0] < a[0])) ==> MergeSeq(a, b)[0] == b[0]
    ensures |a| > 0 ==> MergeSeq(a, b)[0] <= a[0]
    ensures |b| > 0 ==> MergeSeq(a, b)[0] <= b[0]
{
}

lemma MergeSeqLength(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures |MergeSeq(a, b)| == |a| + |b|
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqLength(a[1..], b);
    } else {
        MergeSeqLength(a, b[1..]);
    }
}

lemma MergeSeqMultiset(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    decreases |a| + |b|
{
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqMultiset(a[1..], b);
        assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        assert a == [a[0]] + a[1..];
        assert multiset(a) == multiset([a[0]]) + multiset(a[1..]);
    } else {
        MergeSeqMultiset(a, b[1..]);
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        assert b == [b[0]] + b[1..];
        assert multiset(b) == multiset([b[0]]) + multiset(b[1..]);
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
        invariant Sorted(a[i..]) && Sorted(b[j..])
        invariant Sorted(c[..i+j])
        invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        invariant i + j > 0 && i < a.Length ==> c[i+j-1] <= a[i]
        invariant i + j > 0 && j < b.Length ==> c[i+j-1] <= b[j]
        decreases a.Length - i + b.Length - j
    {
        if i < a.Length && (j == b.Length || a[i] <= b[j]) {
            c[j + i] := a[i];
            
            assert a[..i+1] == a[..i] + [a[i]];
            assert c[..i+j+1] == c[..i+j] + [a[i]];
            
            MergeSeqExtendA(a[..i], b[..j], a[i]);
            
            i := i + 1;
        } 
        else {
            c[i + j] := b[j];
            
            assert b[..j+1] == b[..j] + [b[j]];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            
            MergeSeqExtendB(a[..i], b[..j], b[j]);
            
            j := j + 1;
        }
    }
    assert a[..] == a[..a.Length];
    assert b[..] == b[..b.Length];
}

lemma MergeSeqExtendA(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |a| == 0 || a[|a|-1] <= x
    requires |b| == 0 || x <= b[0]
    requires Sorted(a + [x])
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 {
        if |b| == 0 {
        } else {
            assert x <= b[0];
            assert MergeSeq([x], b) == [x] + MergeSeq([], b);
            assert MergeSeq([], b) == b;
            assert MergeSeq([x], b) == [x] + b;
            assert MergeSeq([], b) + [x] == b + [x];
            MergeSeqAppendSmall(b, x);
        }
    } else if |b| == 0 {
        assert MergeSeq(a + [x], []) == a + [x];
        assert MergeSeq(a, []) == a;
    } else {
        if a[0] <= b[0] {
            assert (a + [x])[0] == a[0];
            assert (a + [x])[1..] == a[1..] + [x];
            assert Sorted(a[1..] + [x]);
            MergeSeqExtendA(a[1..], b, x);
        } else {
            MergeSeqExtendA(a, b[1..], x);
        }
    }
}

lemma MergeSeqAppendSmall(b: seq<int>, x: int)
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    ensures [x] + b == b + [x] || MergeSeq([x], b) == [x] + b
    ensures MergeSeq([x], b) == [x] + b
{
}

lemma MergeSeqExtendB(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |b| == 0 || b[|b|-1] <= x
    requires |a| == 0 || x < a[0]
    requires Sorted(b + [x])
    ensures MergeSeq(a, b + [x]) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |b| == 0 {
        if |a| == 0 {
        } else {
            assert x < a[0];
            MergeSeqAppendSmallB(a, x);
        }
    } else if |a| == 0 {
        assert MergeSeq([], b + [x]) == b + [x];
        assert MergeSeq([], b) == b;
    } else {
        if a[0] <= b[0] {
            MergeSeqExtendB(a[1..], b, x);
        } else {
            assert (b + [x])[0] == b[0];
            assert (b + [x])[1..] == b[1..] + [x];
            assert Sorted(b[1..] + [x]);
            MergeSeqExtendB(a, b[1..], x);
        }
    }
}

lemma MergeSeqAppendSmallB(a: seq<int>, x: int)
    requires Sorted(a)
    requires |a| > 0 && x < a[0]
    ensures MergeSeq(a, [x]) == [x] + a
{
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
