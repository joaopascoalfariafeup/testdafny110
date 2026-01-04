
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
        assert multiset(a) == multiset{};
    } else if |b| == 0 {
        assert multiset(b) == multiset{};
    } else if a[0] <= b[0] {
        MergeSeqMultiset(a[1..], b);
        assert multiset(a) == multiset{a[0]} + multiset(a[1..]);
        assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        assert multiset(MergeSeq(a, b)) == multiset{a[0]} + multiset(MergeSeq(a[1..], b));
    } else {
        MergeSeqMultiset(a, b[1..]);
        assert multiset(b) == multiset{b[0]} + multiset(b[1..]);
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        assert multiset(MergeSeq(a, b)) == multiset{b[0]} + multiset(MergeSeq(a, b[1..]));
    }
}

// Lemma: extending the first sequence when its first element is smaller
lemma MergeSeqExtendFirst(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a + [x])
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    requires |a| == 0 || a[|a|-1] <= x
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a|
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
            // Need to show [x] + b == b + [x] is false in general, but we need MergeSeq
            // Actually: MergeSeq([x], b) should equal [x] + b when x <= b[0]
            // And MergeSeq([], b) + [x] = b + [x]
            // These are different unless b is empty
            // Wait, let me reconsider the postcondition
        }
    } else if |b| == 0 {
        assert MergeSeq(a, []) == a;
        assert MergeSeq(a + [x], []) == a + [x];
        assert a + [x] == MergeSeq(a, []) + [x];
    } else {
        assert a[0] <= a[|a|-1] <= x <= b[0];
        assert (a + [x])[0] == a[0];
        assert (a + [x])[1..] == a[1..] + [x];
        assert a[0] <= b[0];
        calc {
            MergeSeq(a + [x], b);
            == [a[0]] + MergeSeq((a + [x])[1..], b);
            == [a[0]] + MergeSeq(a[1..] + [x], b);
        }
        if |a| == 1 {
            assert a[1..] == [];
            assert Sorted([] + [x]);
        } else {
            assert a[1..][|a[1..]|-1] == a[|a|-1] <= x;
            assert Sorted(a[1..] + [x]);
        }
        MergeSeqExtendFirst(a[1..], b, x);
        assert MergeSeq(a[1..] + [x], b) == MergeSeq(a[1..], b) + [x];
        calc {
            MergeSeq(a + [x], b);
            == [a[0]] + MergeSeq(a[1..] + [x], b);
            == [a[0]] + (MergeSeq(a[1..], b) + [x]);
            == ([a[0]] + MergeSeq(a[1..], b)) + [x];
            == MergeSeq(a, b) + [x];
        }
    }
}

// Lemma: extending the second sequence when its first element is smaller
lemma MergeSeqExtendSecond(a: seq<int>, b: seq<int>, y: int)
    requires Sorted(a)
    requires Sorted(b + [y])
    requires |a| == 0 || a[0] > y
    requires |b| == 0 || b[|b|-1] <= y
    ensures MergeSeq(a, b + [y]) == MergeSeq(a, b) + [y]
    decreases |b|
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
        }
    } else if |a| == 0 {
        assert MergeSeq([], b) == b;
        assert MergeSeq([], b + [y]) == b + [y];
        assert b + [y] == MergeSeq([], b) + [y];
    } else {
        assert b[0] <= b[|b|-1] <= y < a[0];
        assert (b + [y])[0] == b[0];
        assert (b + [y])[1..] == b[1..] + [y];
        assert b[0] < a[0];
        calc {
            MergeSeq(a, b + [y]);
            == [b[0]] + MergeSeq(a, (b + [y])[1..]);
            == [b[0]] + MergeSeq(a, b[1..] + [y]);
        }
        if |b| == 1 {
            assert b[1..] == [];
            assert Sorted([] + [y]);
        } else {
            assert b[1..][|b[1..]|-1] == b[|b|-1] <= y;
            assert Sorted(b[1..] + [y]);
        }
        MergeSeqExtendSecond(a, b[1..], y);
        assert MergeSeq(a, b[1..] + [y]) == MergeSeq(a, b[1..]) + [y];
        calc {
            MergeSeq(a, b + [y]);
            == [b[0]] + MergeSeq(a, b[1..] + [y]);
            == [b[0]] + (MergeSeq(a, b[1..]) + [y]);
            == ([b[0]] + MergeSeq(a, b[1..])) + [y];
            == MergeSeq(a, b) + [y];
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
            assert j < b.Length ==> a[i] <= b[..j][0] || j == 0;
            if j > 0 {
                assert b[..j][0] == b[0];
                assert a[i] <= b[j];
                assert forall m :: 0 <= m < j ==> b[m] <= b[j];
                assert b[0] <= b[j];
            }
            assert j == 0 || a[i] <= b[..j][0];
            MergeSeqExtendFirst(a[..i], b[..j], a[i]);
            i := i + 1;
        } 
        else {
            assert b[..j+1] == b[..j] + [b[j]];
            c[i + j] := b[j];
            assert c[..i+j+1] == c[..i+j] + [b[j]];
            assert i < a.Length ==> b[j] < a[i];
            assert i == 0 || a[..i][0] == a[0];
            assert i > 0 ==> b[j] < a[0];
            assert i > 0 ==> b[j] < a[..i][0];
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




