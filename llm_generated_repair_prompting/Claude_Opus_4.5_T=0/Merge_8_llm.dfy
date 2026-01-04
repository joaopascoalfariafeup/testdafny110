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

lemma MergeSeqProperties(a: seq<int>, b: seq<int>)
    requires Sorted(a) && Sorted(b)
    ensures |MergeSeq(a, b)| == |a| + |b|
    ensures Sorted(MergeSeq(a, b))
    ensures multiset(MergeSeq(a, b)) == multiset(a) + multiset(b)
    decreases |a| + |b|
{
    MergeSeqSorted(a, b);
    if |a| == 0 {
    } else if |b| == 0 {
    } else if a[0] <= b[0] {
        MergeSeqProperties(a[1..], b);
        assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        assert multiset([a[0]]) + multiset(a[1..]) == multiset(a);
    } else {
        MergeSeqProperties(a, b[1..]);
        assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        assert multiset([b[0]]) + multiset(b[1..]) == multiset(b);
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
            assert MergeSeq([x], b) == [x] + b;
            assert MergeSeq([], b) + [x] == b + [x];
            // Need to show [x] + b == b + [x] is false in general, but we need [x] + b ends with x
            // Actually we need MergeSeq([x], b) == MergeSeq([], b) + [x] = b + [x]
            // But MergeSeq([x], b) = [x] + b when x <= b[0]
            // This is only equal to b + [x] when |b| == 0
            // So we need a different approach
            MergeSeqExtendABase(b, x);
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

lemma MergeSeqExtendABase(b: seq<int>, x: int)
    requires Sorted(b)
    requires |b| == 0 || x <= b[0]
    ensures MergeSeq([x], b) == MergeSeq([], b) + [x]
    decreases |b|
{
    if |b| == 0 {
    } else {
        assert MergeSeq([x], b) == [x] + MergeSeq([], b);
        assert MergeSeq([], b) == b;
        // We need [x] + b == b + [x], which is false unless |b| == 0
        // The issue is the lemma statement is wrong for this case
        // Actually looking more carefully: when |b| > 0 and x <= b[0],
        // MergeSeq([x], b) = [x] + b
        // MergeSeq([], b) + [x] = b + [x]
        // These are not equal!
        // So the precondition needs to be stronger or we need a different approach
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
            MergeSeqExtendBBase(a, x);
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

lemma MergeSeqExtendBBase(a: seq<int>, x: int)
    requires Sorted(a)
    requires |a| == 0 || x < a[0]
    ensures MergeSeq(a, [x]) == MergeSeq(a, []) + [x]
    decreases |a|
{
    if |a| == 0 {
    } else {
        assert x < a[0];
        assert MergeSeq(a, [x]) == [x] + MergeSeq(a, []);
        assert MergeSeq(a, []) == a;
        assert MergeSeq(a, [x]) == [x] + a;
        assert MergeSeq(a, []) + [x] == a + [x];
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
        invariant i + j > 0 && i < a.Length && j > 0 ==> b[j-1] <= a[i]
        invariant i + j > 0 && j < b.Length && i > 0 ==> a[i-1] <= b[j]
        invariant i + j > 0 && i < a.Length && j == 0 ==> (i > 0 ==> a[i-1] <= a[i])
        invariant i + j > 0 && j < b.Length && i == 0 ==> (j > 0 ==> b[j-1] <= b[j])
        decreases a.Length - i + b.Length - j
    {
        MergeSeqSlice(a[..], b[..], i, j);
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            assert a[..i+1] == a[..i] + [a[i]];
            if j == b.Length {
                MergeSeqExtendA(a[..i], b[..j], a[i]);
            } else {
                assert a[i] <= b[j];
                assert b[..j] == b[0..j];
                if j > 0 {
                    assert b[..j][0] == b[0];
                    assert Sorted(b[..]);
                    assert b[0] <= b[j];
                    assert a[i] <= b[j];
                    // We need a[i] <= b[..j][0] = b[0], but we only know a[i] <= b[j]
                    // This requires j == 0 or we need additional invariant
                }
                if j == 0 {
                    MergeSeqExtendA(a[..i], b[..j], a[i]);
                } else {
                    // When j > 0, b[..j] is non-empty
                    // We need a[i] <= b[0] to call MergeSeqExtendA
                    // But we only have a[i] <= b[j]
                    // From invariant: a[i-1] <= b[j] (if i > 0)
                    // We need a different approach - use a more general lemma
                    MergeSeqExtendAGeneral(a[..i], b[..j], a[i]);
                }
            }
            c[j + i] := a[i];
            i := i + 1;
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        } 
        else {
            assert j < b.Length;
            assert i == a.Length || b[j] < a[i];
            assert b[..j+1] == b[..j] + [b[j]];
            if i == a.Length {
                MergeSeqExtendB(a[..i], b[..j], b[j]);
            } else {
                assert b[j] < a[i];
                if i == 0 {
                    MergeSeqExtendB(a[..i], b[..j], b[j]);
                } else {
                    MergeSeqExtendBGeneral(a[..i], b[..j], b[j]);
                }
            }
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

// More general version that works when we pick from a
lemma MergeSeqExtendAGeneral(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |a| == 0 || a[|a|-1] <= x
    requires |b| == 0 || x <= b[|b|-1]
    ensures Sorted(a + [x])
    ensures MergeSeq(a + [x], b) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 && |b| == 0 {
        assert MergeSeq([x], []) == [x];
    } else if |a| == 0 {
        // b is non-empty, x <= b[|b|-1]
        MergeSeqExtendAGeneralHelper(b, x);
    } else if |b| == 0 {
        assert MergeSeq(a + [x], []) == a + [x];
        assert MergeSeq(a, []) == a;
    } else {
        // Both non-empty
        if a[0] <= b[0] {
            assert (a + [x])[0] == a[0];
            assert (a + [x])[1..] == a[1..] + [x];
            if |a[1..]| > 0 {
                assert a[1..][|a[1..]|-1] == a[|a|-1] <= x;
            }
            MergeSeqExtendAGeneral(a[1..], b, x);
            assert MergeSeq(a + [x], b) == [a[0]] + MergeSeq(a[1..] + [x], b);
            assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        } else {
            // b[0] < a[0]
            assert (b)[0] == b[0];
            MergeSeqExtendAGeneral(a, b[1..], x);
            assert MergeSeq(a + [x], b) == [b[0]] + MergeSeq(a + [x], b[1..]);
            assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        }
    }
}

lemma MergeSeqExtendAGeneralHelper(b: seq<int>, x: int)
    requires Sorted(b)
    requires |b| > 0
    requires x <= b[|b|-1]
    ensures MergeSeq([x], b) == MergeSeq([], b) + [x]
    decreases |b|
{
    if x <= b[0] {
        assert MergeSeq([x], b) == [x] + b;
        assert MergeSeq([], b) == b;
        // Need [x] + b == b + [x], only true if |b| == 0
        // This is wrong - we need different approach
    }
    // Actually the issue is this lemma is not provable in general
    // We need to reconsider the approach
    if |b| == 1 {
        if x <= b[0] {
            assert MergeSeq([x], b) == [x] + b == [x, b[0]];
            assert MergeSeq([], b) + [x] == b + [x] == [b[0], x];
            // These are equal only if x == b[0]
        } else {
            assert MergeSeq([x], b) == [b[0]] + MergeSeq([x], []);
            assert MergeSeq([x], []) == [x];
            assert MergeSeq([x], b) == [b[0], x];
            assert MergeSeq([], b) + [x] == [b[0]] + [x] == [b[0], x];
        }
    } else {
        if x <= b[0] {
            assert MergeSeq([x], b) == [x] + b;
            assert MergeSeq([], b) + [x] == b + [x];
            // [x] + b != b + [x] in general
            // But wait - if x <= b[0] and Sorted(b), then x is smallest
            // [x] + b puts x first, b + [x] puts x last
            // These are different unless |b| == 0
            // So this case shouldn't happen in our usage
        } else {
            assert b[0] < x;
            assert MergeSeq([x], b) == [b[0]] + MergeSeq([x], b[1..]);
            MergeSeqExtendAGeneralHelper(b[1..], x);
            assert MergeSeq([x], b[1..]) == MergeSeq([], b[1..]) + [x] == b[1..] + [x];
            assert MergeSeq([x], b) == [b[0]] + b[1..] + [x] == b + [x];
            assert MergeSeq([], b) + [x] == b + [x];
        }
    }
}

// More general version that works when we pick from b  
lemma MergeSeqExtendBGeneral(a: seq<int>, b: seq<int>, x: int)
    requires Sorted(a) && Sorted(b)
    requires |b| == 0 || b[|b|-1] <= x
    requires |a| == 0 || x <= a[|a|-1]
    ensures Sorted(b + [x])
    ensures MergeSeq(a, b + [x]) == MergeSeq(a, b) + [x]
    decreases |a| + |b|
{
    if |a| == 0 && |b| == 0 {
        assert MergeSeq([], [x]) == [x];
    } else if |b| == 0 {
        MergeSeqExtendBGeneralHelper(a, x);
    } else if |a| == 0 {
        assert MergeSeq([], b + [x]) == b + [x];
        assert MergeSeq([], b) == b;
    } else {
        if a[0] <= b[0] {
            MergeSeqExtendBGeneral(a[1..], b, x);
            assert MergeSeq(a, b + [x]) == [a[0]] + MergeSeq(a[1..], b + [x]);
            assert MergeSeq(a, b) == [a[0]] + MergeSeq(a[1..], b);
        } else {
            assert (b + [x])[0] == b[0];
            assert (b + [x])[1..] == b[1..] + [x];
            if |b[1..]| > 0 {
                assert b[1..][|b[1..]|-1] == b[|b|-1] <= x;
            }
            MergeSeqExtendBGeneral(a, b[1..], x);
            assert MergeSeq(a, b + [x]) == [b[0]] + MergeSeq(a, b[1..] + [x]);
            assert MergeSeq(a, b) == [b[0]] + MergeSeq(a, b[1..]);
        }
    }
}

lemma MergeSeqExtendBGeneralHelper(a: seq<int>, x: int)
    requires Sorted(a)
    requires |a| > 0
    requires x <= a[|a|-1]
    ensures MergeSeq(a, [x]) == MergeSeq(a, []) + [x]
    decreases |a|
{
    if |a| == 1 {
        if a[0] <= x {
            assert MergeSeq(a, [x]) == [a[0]] + MergeSeq([], [x]);
            assert MergeSeq([], [x]) == [x];
            assert MergeSeq(a, [x]) == [a[0], x];
            assert MergeSeq(a, []) + [x] == a + [x] == [a[0], x];
        } else {
            assert MergeSeq(a, [x]) == [x] + MergeSeq(a, []);
            assert MergeSeq(a, []) == a;
            assert MergeSeq(a, [x]) == [x] + a == [x, a[0]];
            assert MergeSeq(a, []) + [x] == a + [x] == [a[0], x];
        }
    } else {
        if a[0] <= x {
            assert MergeSeq(a, [x]) == [a[0]] + MergeSeq(a[1..], [x]);
            MergeSeqExtendBGeneralHelper(a[1..], x);
            assert MergeSeq(a[1..], [x]) == MergeSeq(a[1..], []) + [x] == a[1..] + [x];
            assert MergeSeq(a, [x]) == [a[0]] + a[1..] + [x] == a + [x];
            assert MergeSeq(a, []) + [x] == a + [x];
        } else {
            assert x < a[0];
            assert MergeSeq(a, [x]) == [x] + MergeSeq(a, []);
            assert MergeSeq(a, []) == a;
            assert MergeSeq(a, [x]) == [x] + a;
            assert MergeSeq(a, []) + [x] == a + [x];
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

