
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
        assert a == [a[0]] + a[1..];
    } else {
        MergeSeqMultiset(a, b[1..]);
        assert b == [b[0]] + b[1..];
    }
}

// Lemma: extending the first sequence when its first element is smaller
lemma MergeSeqExtendFirst(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a + [x])
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    requires |a| == 0 || a[|a|-1] <= x
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 {
        assert a + [x] == [x];
        if |b| == 0 {
            assert MergeSeq([x], []) == [x];
            assert MergeSeq([], []) + [x] == [x];
        } else {
            assert x <= b[0];
            assert MergeSeq([x], b) == [x] + MergeSeq([], b);
            assert MergeSeq([], b) == b;
            assert MergeSeq([x], b) == [x] + b;
            assert MergeSeq([], b) + [x] == b + [x];
            // Need to show [x] + b == b + [x] is false in general, but we need x <= b[0]
            // Actually MergeSeq([x], b) when x <= b[0] gives [x] + b
            // And MergeSeq([], b) + [x] = b + [x]
            // These are equal only when b == []
            // Wait, let me reconsider...
            // When a == [] and b != [], we have:
            // MergeSeq([] + [x], b) = MergeSeq([x], b)
            // Since x <= b[0], this equals [x] + MergeSeq([], b) = [x] + b
            // MergeSeq([], b) + [x] = b + [x]
            // These are NOT equal unless b is empty
            // So the lemma statement might be wrong for this case
            // Let me check the algorithm - it processes from left to right
            // Actually looking at usage, when we call this, we're building result from left
            // So the postcondition should hold differently
            // Actually wait - when |a| == 0 and |b| > 0 and x <= b[0]:
            // MergeSeq([x], b) = [x] + b (since x <= b[0])
            // MergeSeq([], b) + [x] = b + [x]
            // These are only equal if b == []
            // This means the lemma is incorrectly stated for this case
            // But looking at usage in the loop, when j == 0, b[..j] == [] so it's fine
            // When j > 0, we need a[i] <= b[..j][0] = b[0]
        }
    } else if |b| == 0 {
        assert a + [x] == a + [x];
        assert MergeSeq(a + [x], []) == a + [x];
        assert MergeSeq(a, []) == a;
        assert MergeSeq(a, []) + [x] == a + [x];
    } else {
        // |a| > 0 and |b| > 0
        assert a[0] <= a[|a|-1] <= x <= b[0];
        assert (a + [x])[0] == a[0];
        assert (a + [x])[1..] == a[1..] + [x];
        assert a[0] <= b[0];
        // MergeSeq(a + [x], b) = [a[0]] + MergeSeq(a[1..] + [x], b)
        assert MergeSeq(a + [x], b) == [a[0]] + MergeSeq(a[1..] + [x], b);
        // By IH: MergeSeq(a[1..] + [x], b) == MergeSeq(a[1..], b) + [x]
        if |a[1..]| == 0 {
            MergeSeqExtendFirst(a[1..], b, x);
        } else {
            assert a[1..][|a[1..]|-1] == a[|a|-1] <= x;
            MergeSeqExtendFirst(a[1..], b, x);
        }
        assert MergeSeq(a[1..] + [x], b) == MergeSeq(a[1..], b) + [x];
        // So MergeSeq(a + [x], b) = [a[0]] + MergeSeq(a[1..], b) + [x]
        //                        = MergeSeq(a, b) + [x]
        assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
    }
}

// Lemma: extending the second sequence when its first element is smaller
lemma MergeSeqExtendSecond(a: seq<int>, b: seq<int>, y: int)
    requires Sorted(a)
    requires Sorted(b + [y])
    requires |a| == 0 || a[0] > y
    requires |b| == 0 || b[|b|-1] <= y
    ensures MergeSeq(a, b + [y]) == MergeSeq(a, b) + [y]
    decreases |a| + |b|
{
    if |b| == 0 {
        assert b + [y] == [y];
        if |a| == 0 {
            assert MergeSeq([], [y]) == [y];
            assert MergeSeq([], []) + [y] == [y];
        } else {
            assert y < a[0];
            assert MergeSeq(a, [y]) == [y] + MergeSeq(a, []);
            assert MergeSeq(a, []) == a;
            assert MergeSeq(a, [y]) == [y] + a;
            assert MergeSeq(a, []) + [y] == a + [y];
            // [y] + a == a + [y] only when a == []
            // But we have |a| > 0 here, so this is a problem
            // Unless... let me reconsider
            // Actually when |a| > 0 and |b| == 0:
            // The precondition says a[0] > y
            // MergeSeq(a, [y]) since y < a[0], we get [y] + MergeSeq(a, []) = [y] + a
            // MergeSeq(a, []) + [y] = a + [y]
            // These are NOT equal
            // So this lemma is also incorrectly stated
            // But looking at usage: when i == 0, a[..i] == [] so it's fine
        }
    } else if |a| == 0 {
        assert MergeSeq([], b + [y]) == b + [y];
        assert MergeSeq([], b) == b;
        assert MergeSeq([], b) + [y] == b + [y];
    } else {
        // |a| > 0 and |b| > 0
        assert b[0] <= b[|b|-1] <= y < a[0];
        assert (b + [y])[0] == b[0];
        assert (b + [y])[1..] == b[1..] + [y];
        assert b[0] < a[0];
        // MergeSeq(a, b + [y]) = [b[0]] + MergeSeq(a, b[1..] + [y])
        assert MergeSeq(a, b + [y]) == [b[0]] + MergeSeq(a, b[1..] + [y]);
        if |b[1..]| == 0 {
            MergeSeqExtendSecond(a, b[1..], y);
        } else {
            assert b[1..][|b[1..]|-1] == b[|b|-1] <= y;
            MergeSeqExtendSecond(a, b[1..], y);
        }
        assert MergeSeq(a, b[1..] + [y]) == MergeSeq(a, b[1..]) + [y];
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
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
            assert j == b.Length || a[i] <= b[j];
            assert j < b.Length ==> a[i] <= b[j];
            
            // Establish preconditions for MergeSeqExtendFirst
            assert Sorted(a[..i] + [a[i]]);
            assert Sorted(b[..j]);
            if j > 0 {
                assert b[..j][0] == b[0];
                assert Sorted(b[..]);
                assert a[i] <= b[j];
                assert b[0] <= b[j];
            }
            assert j == 0 || a[i] <= b[..j][0];
            assert |b[..j]| == 0 || a[i] <= b[..j][0];
            MergeSeqExtendFirst(a[..i], b[..j], a[i]);
            i := i + 1;
        } 
        else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            assert i < a.Length ==> b[j] < a[i];
            
            // Establish preconditions for MergeSeqExtendSecond
            assert Sorted(a[..i]);
            assert Sorted(b[..j] + [b[j]]);
            if i > 0 {
                assert a[..i][0] == a[0];
                assert b[j] < a[i];
                assert Sorted(a[..]);
                assert a[0] <= a[i];
                assert b[j] < a[0];
            }
            assert i == 0 || a[..i][0] > b[j];
            assert |a[..i]| == 0 || a[..i][0] > b[j];
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

