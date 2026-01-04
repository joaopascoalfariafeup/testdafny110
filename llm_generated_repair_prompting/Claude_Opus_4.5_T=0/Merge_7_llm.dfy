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
        assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
    } else {
        MergeSeqProperties(a, b[1..]);
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
    }
}

// Lemma to connect slices with full arrays
lemma MergeSeqSlice(a: seq<int>, b: seq<int>, i: int, j: int)
    requires Sorted(a) && Sorted(b)
    requires 0 <= i <= |a| && 0 <= j <= |b|
    ensures Sorted(a[i..]) && Sorted(b[j..])
    ensures Sorted(a[..i]) && Sorted(b[..j])
{
}

// Key lemma: extending a by one element at the end
lemma MergeSeqExtendA(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |a| == 0 || a[|a|-1] <= x
    requires |b| == 0 || x <= b[0]
    ensures Sorted(a + [x])
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 {
        if |b| == 0 {
            assert MergeSeq([x], b) == [x];
        } else {
            assert x <= b[0];
            assert MergeSeq([x], b) == [x] + MergeSeq([], b);
            assert MergeSeq([], b) == b;
        }
    } else {
        assert Sorted(a[1..]);
        if |a[1..]| > 0 {
            assert a[1..][|a[1..]|-1] == a[|a|-1] <= x;
        }
        MergeSeqExtendA(a[1..], b, x);
        assert (a + [x])[1..] == a[1..] + [x];
        if |b| == 0 {
            assert MergeSeq(a + [x], b) == a + [x];
            assert MergeSeq(a, b) == a;
        } else {
            assert a[0] == (a + [x])[0];
            assert a[0] <= x <= b[0];
            assert MergeSeq(a + [x], b) == [a[0]] + MergeSeq(a[1..] + [x], b);
            assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        }
    }
}

// Key lemma: extending b by one element at the end
lemma MergeSeqExtendB(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |b| == 0 || b[|b|-1] <= x
    requires |a| == 0 || x < a[0]
    ensures Sorted(b + [x])
    ensures MergeSeq(a, b + [x]) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |b| == 0 {
        if |a| == 0 {
            assert MergeSeq(a, [x]) == [x];
        } else {
            assert x < a[0];
            assert MergeSeq(a, [x]) == [x] + MergeSeq(a, []);
            assert MergeSeq(a, []) == a;
        }
    } else {
        assert Sorted(b[1..]);
        if |b[1..]| > 0 {
            assert b[1..][|b[1..]|-1] == b[|b|-1] <= x;
        }
        MergeSeqExtendB(a, b[1..], x);
        assert (b + [x])[1..] == b[1..] + [x];
        if |a| == 0 {
            assert MergeSeq(a, b + [x]) == b + [x];
            assert MergeSeq(a, b) == b;
        } else {
            assert b[0] == (b + [x])[0];
            assert b[0] <= x < a[0];
            assert MergeSeq(a, b + [x]) == [b[0]] + MergeSeq(a, b[1..] + [x]);
            assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        }
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
        invariant Sorted(a[i..]) && Sorted(b[j..])
        invariant Sorted(a[..i]) && Sorted(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        invariant i + j > 0 && i < a.Length ==> (j == 0 || b[j-1] <= a[i])
        invariant i + j > 0 && j < b.Length ==> (i == 0 || a[i-1] <= b[j])
        decreases a.Length - i + b.Length - j
    {
        MergeSeqSlice(a[..], b[..], i, j);
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            MergeSeqExtendA(a[..i], b[..j], a[i]);
            c[j + i] := a[i];
            i := i + 1;
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        } 
        else {
            assert j < b.Length;
            assert b[..j+1] == b[..j] + [b[j]];
            MergeSeqExtendB(a[..i], b[..j], b[j]);
            c[i + j] := b[j];
            j := j + 1;
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
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
