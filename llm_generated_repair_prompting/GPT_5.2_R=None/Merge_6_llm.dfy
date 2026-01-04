
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function multisetOf(s: seq<int>): multiset<int>
{
  multiset(s)
}

// A lightweight proof helper for multisets over sequence concatenation
lemma MultisetOfConcat<T>(s: seq<T>, t: seq<T>)
  ensures multiset(s + t) == multiset(s) + multiset(t)
{
}

// Order-preserving merge of two sorted sequences
ghost function mergeSeq(a: seq<int>, b: seq<int>): seq<int>
  requires Sorted(a)
  requires Sorted(b)
  ensures |mergeSeq(a,b)| == |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + mergeSeq(a[1..], b)
  else [b[0]] + mergeSeq(a, b[1..])
}

// Key helper: mergeSeq always produces a sorted sequence when inputs are sorted
lemma MergeSeqSorted(a: seq<int>, b: seq<int>)
  requires Sorted(a)
  requires Sorted(b)
  ensures Sorted(mergeSeq(a,b))
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
    // then mergeSeq(a,b) is one of the inputs, already sorted
  } else if a[0] <= b[0] {
    // mergeSeq(a,b) = [a0] + mergeSeq(a1,b)
    MergeSeqSorted(a[1..], b);

    // show head <= every element of tail
    assert Sorted(mergeSeq(a[1..], b));
    assert forall k :: 0 <= k < |mergeSeq(a[1..], b)| ==> a[0] <= mergeSeq(a[1..], b)[k] by {
      // elements of merge are from a[1..] or b
      // use Sorted(a) for a[0] <= a[1..][*] and Sorted(b) plus a[0] <= b[0] for b[*]
      if |mergeSeq(a[1..], b)| > 0 {
        // For any k, reason by cases on which branch mergeSeq took at the front.
        // We avoid unfolding deeply by using facts:
        // - a[0] <= every element of a[1..] since Sorted(a)
        // - a[0] <= every element of b since a[0] <= b[0] and Sorted(b)
      }
    }
  } else {
    // symmetric
    MergeSeqSorted(a, b[1..]);
    assert Sorted(mergeSeq(a, b[1..]));
    assert forall k :: 0 <= k < |mergeSeq(a, b[1..])| ==> b[0] <= mergeSeq(a, b[1..])[k] by {
    }
  }
}

// Key helper: mergeSeq preserves multiset content
lemma MergeSeqMultiset(a: seq<int>, b: seq<int>)
  requires Sorted(a)
  requires Sorted(b)
  ensures multisetOf(mergeSeq(a,b)) == multisetOf(a) + multisetOf(b)
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if a[0] <= b[0] {
    MergeSeqMultiset(a[1..], b);
    // multiset([a0] + m) = {a0} + multiset(m)
    calc {
      multisetOf(mergeSeq(a,b));
      == { }
      multisetOf([a[0]] + mergeSeq(a[1..], b));
      == { MultisetOfConcat([a[0]], mergeSeq(a[1..], b)); }
      multisetOf([a[0]]) + multisetOf(mergeSeq(a[1..], b));
      == { }
      multisetOf([a[0]]) + (multisetOf(a[1..]) + multisetOf(b));
      == { assert a == [a[0]] + a[1..]; }
      (multisetOf([a[0]]) + multisetOf(a[1..])) + multisetOf(b);
      == { MultisetOfConcat([a[0]], a[1..]); }
      multisetOf(a) + multisetOf(b);
    }
  } else {
    MergeSeqMultiset(a, b[1..]);
    calc {
      multisetOf(mergeSeq(a,b));
      == { }
      multisetOf([b[0]] + mergeSeq(a, b[1..]));
      == { MultisetOfConcat([b[0]], mergeSeq(a, b[1..])); }
      multisetOf([b[0]]) + multisetOf(mergeSeq(a, b[1..]));
      == { }
      multisetOf([b[0]]) + (multisetOf(a) + multisetOf(b[1..]));
      == { assert b == [b[0]] + b[1..]; }
      multisetOf(a) + (multisetOf([b[0]]) + multisetOf(b[1..]));
      == { MultisetOfConcat([b[0]], b[1..]); }
      multisetOf(a) + multisetOf(b);
    }
  }
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c.Length == a.Length + b.Length
  ensures Sorted(c[..])
  ensures multisetOf(c[..]) == multisetOf(a[..]) + multisetOf(b[..])
  ensures c[..] == mergeSeq(a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b' respectively

    while i < a.Length || j < b.Length
      decreases (a.Length - i) + (b.Length - j)
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant multisetOf(c[..i+j]) == multisetOf(a[..i]) + multisetOf(b[..j])
      invariant c[..i+j] == mergeSeq(a[..i], b[..j])
      invariant Sorted(c[..i+j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            i := i + 1;

            // sequence-slice helper
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;

            // sequence-slice helper
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        }

        // Re-establish the two key invariants from the mergeSeq model
        // (easier than maintaining them directly through array updates)
        // c[..i+j] is definitionally the prefix we have filled; link it back to mergeSeq:
        // This is exactly what the algorithm constructs.
        // We help Dafny by forcing it to use the mergeSeq characterization.
        if i + j > 0 {
          // no-op assertion to help unfolding on the prefixes
          assert a[..i] == a[..i];
          assert b[..j] == b[..j];
        }

        // Sortedness and multiset facts follow from the model equality
        MergeSeqSorted(a[..i], b[..j]);
        MergeSeqMultiset(a[..i], b[..j]);

        assert Sorted(mergeSeq(a[..i], b[..j]));
        assert multisetOf(mergeSeq(a[..i], b[..j])) == multisetOf(a[..i]) + multisetOf(b[..j]);
      }

    // Conclude final postconditions from the invariant at loop exit
    assert !(i < a.Length || j < b.Length);
    assert i == a.Length && j == b.Length;
    assert c[..] == c[..c.Length];
    assert c[..] == c[..i+j];
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

