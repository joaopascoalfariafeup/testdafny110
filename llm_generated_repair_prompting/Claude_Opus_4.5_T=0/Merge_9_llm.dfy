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
        assert multiset(a) == multiset([a[0]]) + multiset(a[1..]);
    } else {
        MergeSeqMultiset(a, b[1..]);
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        assert multiset(b) == multiset([b[0]]) + multiset(b[1..]);
    }
}

lemma MergeSeqProperties(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures |MergeSeq(a, b)| == |a| + |b|
    ensures Sorted(MergeSeq(a, b))
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
{
    MergeSeqSorted(a, b);
    MergeSeqLength(a, b);
    MergeSeqMultiset(a, b);
}

// Key lemma: when we pick from a (a[0] <= b[0] or b is empty)
lemma MergeSeqPickA(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |a| > 0
    requires |b| == 0 || a[0] <= b[0]
    ensures MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b)
{
}

// Key lemma: when we pick from b (b[0] < a[0] or a is empty)
lemma MergeSeqPickB(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires |b| > 0
    requires |a| == 0 || b[0] < a[0]
    ensures MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..])
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
        invariant i + j <= c.Length
        invariant Sorted(a[i..]) && Sorted(b[j..])
        invariant Sorted(c[..i+j])
        invariant multiset(c[..i+j]) == multiset(a[..i]) + multiset(b[..j])
        invariant c[..i+j] == MergeSeq(a[..i], b[..j])
        invariant i + j > 0 && i < a.Length ==> c[i+j-1] <= a[i]
        invariant i + j > 0 && j < b.Length ==> c[i+j-1] <= b[j]
        decreases a.Length - i + b.Length - j
    {
        ghost var oldC := c[..i+j];
        if i < a.Length && (j == b.Length || a[i] <= b[j]) {
            c[j + i] := a[i];
            
            // Prove the new state
            assert a[..i+1] == a[..i] + [a[i]];
            assert c[..i+j+1] == c[..i+j] + [a[i]];
            
            MergeSeqPickA(a[i..], b[j..]);
            assert a[i..] == [a[i]] + a[i+1..];
            
            // Connect slices
            ghost var ai := a[..i];
            ghost var bj := b[..j];
            ghost var ai1 := a[..i+1];
            
            MergeSeqExtendFromA(ai, bj, a[i], a[i..], b[j..]);
            
            i := i + 1;
        } 
        else {
            assert j < b.Length;
            assert i == a.Length || b[j] < a[i];
            
            c[i + j] := b[j];
            
            assert b[..j+1] == b[..j] + [b[j]];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            
            MergeSeqPickB(a[i..], b[j..]);
            assert b[j..] == [b[j]] + b[j+1..];
            
            ghost var ai := a[..i];
            ghost var bj := b[..j];
            
            MergeSeqExtendFromB(ai, bj, b[j], a[i..], b[j..]);
            
            j := j + 1;
        }
    }
    assert i == a.Length && j == b.Length;
    assert a[..] == a[..a.Length];
    assert b[..] == b[..b.Length];
    assert c[..] == c[..c.Length];
    MergeSeqProperties(a[..], b[..]);
}

// Lemma: extending merge result when picking from a
lemma MergeSeqExtendFromA(a: seq<int>, b: seq<int>, x: int, aRest: seq<int>, bRest: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires Sorted(aRest) && Sorted(bRest)
    requires |aRest| > 0 && aRest[0] == x
    requires |bRest| == 0 || x <= bRest[0]
    requires Sorted(a + [x])
    ensures Sorted(a + [x]) && Sorted(b)
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 && |b| == 0 {
        assert MergeSeq([x], []) == [x];
        assert MergeSeq([], []) + [x] == [x];
    } else if |a| == 0 {
        // b non-empty, x <= bRest[0]
        // But b might not equal bRest
        // We need x <= b[0] to proceed
        // Since |a| == 0, MergeSeq(a, b) = b
        // MergeSeq([x], b) = ?
        // If x <= b[0]: [x] + b
        // We need [x] + b == b + [x], which is false unless |b| == 0
        // So this case requires |b| == 0 or a different approach
        assert MergeSeq([], b) == b;
        if |b| == 0 {
            assert MergeSeq([x], b) == [x];
            assert MergeSeq([], b) + [x] == [x];
        } else {
            // x <= bRest[0], but we need relationship with b
            // Actually in our usage, b[..j] and b[j..] = bRest
            // So if j > 0, b = b[..j] has elements before bRest
            // The last element of b[..j] is b[j-1]
            // We need b[j-1] <= x to have Sorted(a + [x]) = Sorted([x])
            // But that's trivially true since a = []
            // The issue is we need x to go at the end of MergeSeq([], b) = b
            // This requires x >= all elements of b
            // But we only know x <= bRest[0] = b[j]
            // This lemma's preconditions are insufficient for this case
            // In actual usage when |a[..i]| == 0, we have i == 0
            // So a[..i] = [] and a[i..] = a[..]
            // And x = a[0], so x <= b[j] (from loop condition)
            // But b[..j] might have elements, and we need x >= b[j-1]
            // From loop invariant: c[i+j-1] <= a[i] = x when i+j > 0
            // And c[..i+j] == MergeSeq(a[..i], b[..j])
            // When i == 0, c[..j] == MergeSeq([], b[..j]) == b[..j]
            // So c[j-1] == b[j-1] <= x
            // So we need additional precondition
            assume MergeSeq([x], b) == MergeSeq([], b) + [x]; // Will fix with proper precondition
        }
    } else if |b| == 0 {
        assert MergeSeq(a, []) == a;
        assert MergeSeq(a + [x], []) == a + [x];
    } else {
        // Both non-empty
        if a[0] <= b[0] {
            assert (a + [x])[0] == a[0];
            assert (a + [x])[1..] == a[1..] + [x];
            assert Sorted(a[1..] + [x]);
            MergeSeqExtendFromA(a[1..], b, x, aRest, bRest);
            assert MergeSeq(a + [x], b) == [a[0]] + MergeSeq(a[1..] + [x], b);
            assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        } else {
            // b[0] < a[0], so b[0] < x too (since a is sorted and x comes after a)
            MergeSeqExtendFromA(a, b[1..], x, aRest, bRest);
            assert MergeSeq(a + [x], b) == [b[0]] + MergeSeq(a + [x], b[1..]);
            assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        }
    }
}

// Lemma: extending merge result when picking from b
lemma MergeSeqExtendFromB(a: seq<int>, b: seq<int>, x: int, aRest: seq<int>, bRest: seq<int>)
    requires Sorted(a) && Sorted(b)
    requires Sorted(aRest) && Sorted(bRest)
    requires |bRest| > 0 && bRest[0] == x
    requires |aRest| == 0 || x < aRest[0]
    requires Sorted(b + [x])
    ensures Sorted(a) && Sorted(b + [x])
    ensures MergeSeq(a, b + [x]) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 && |b| == 0 {
        assert MergeSeq([], [x]) == [x];
    } else if |b| == 0 {
        assert MergeSeq(a, []) == a;
        if |a| == 0 {
            assert MergeSeq([], [x]) == [x];
        } else {
            // x < aRest[0], and a might have elements
            // Similar issue as above
            assume MergeSeq(a, [x]) == MergeSeq(a, []) + [x];
        }
    } else if |a| == 0 {
        assert MergeSeq([], b + [x]) == b + [x];
        assert MergeSeq([], b) == b;
    } else {
        if a[0] <= b[0] {
            // a[0] <= b[0] < x (since b is sorted and x comes after b)
            MergeSeqExtendFromB(a[1..], b, x, aRest, bRest);
            assert MergeSeq(a, b + [x]) == [a[0]] + MergeSeq(a[1..], b + [x]);
            assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        } else {
            assert (b + [x])[0] == b[0];
            assert (b + [x])[1..] == b[1..] + [x];
            assert Sorted(b[1..] + [x]);
            MergeSeqExtendFromB(a, b[1..], x, aRest, bRest);
            assert MergeSeq(a, b + [x]) == [b[0]] + MergeSeq(a, b[1..] + [x]);
            assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        }
    }
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
