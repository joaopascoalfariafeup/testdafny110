
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function multisetOf(s: seq<int>): multiset<int>
{
  multiset(s)
}

// A functional (sequence) version of the array merge, matching the implementation's tie-breaking.
ghost function mergeModel(a: seq<int>, b: seq<int>, i: nat, j: nat): seq<int>
  requires i <= |a| && j <= |b|
  requires Sorted(a) && Sorted(b)
  decreases (|a| - i) + (|b| - j)
{
  if i == |a| then b[j..]
  else if j == |b| then a[i..]
  else if a[i] <= b[j] then [a[i]] + mergeModel(a, b, i+1, j)
  else [b[j]] + mergeModel(a, b, i, j+1)
}

lemma MergeModelSorted(a: seq<int>, b: seq<int>, i: nat, j: nat)
  requires i <= |a| && j <= |b|
  requires Sorted(a) && Sorted(b)
  ensures Sorted(mergeModel(a,b,i,j))
  decreases (|a| - i) + (|b| - j)
{
  if i == |a| {
    // mergeModel = b[j..], and any slice of a sorted sequence is sorted
    assert Sorted(b[j..]);
  } else if j == |b| {
    assert Sorted(a[i..]);
  } else if a[i] <= b[j] {
    MergeModelSorted(a, b, i+1, j);
    // show head <= all later elements
    assert forall k :: 0 <= k < |mergeModel(a,b,i+1,j)| ==> a[i] <= mergeModel(a,b,i+1,j)[k] by {
      if i+1 == |a| {
        // tail is b[j..]
        assert forall kk :: 0 <= kk < |b[j..]| ==> b[j..][kk] == b[j+kk];
        assert forall kk :: 0 <= kk < |b[j..]| ==> b[j] <= b[j+kk];
        assert forall kk :: 0 <= kk < |b[j..]| ==> a[i] <= b[j+kk];
      } else {
        // first element of tail is min(a[i+1], b[j]) in the merge, both >= a[i]
        assert a[i] <= a[i+1];
        assert a[i] <= b[j];
      }
      // and in general, all elements produced are from a[i+1..] or b[j..], both >= a[i]
      assert forall t :: 0 <= t < |a| - (i+1) ==> a[i] <= a[i+1+t] by {
        // Sorted(a) gives monotonicity
      }
      assert forall t :: 0 <= t < |b| - j ==> a[i] <= b[j+t] by {
        // since a[i] <= b[j] and Sorted(b)
        assert b[j] <= b[j+t] || t == 0;
      }
    }
    // now list [a[i]] + tail is sorted
    assert Sorted([a[i]] + mergeModel(a,b,i+1,j));
  } else {
    MergeModelSorted(a, b, i, j+1);
    assert forall k :: 0 <= k < |mergeModel(a,b,i,j+1)| ==> b[j] <= mergeModel(a,b,i,j+1)[k] by {
      if j+1 == |b| {
        assert forall kk :: 0 <= kk < |a[i..]| ==> a[i..][kk] == a[i+kk];
        assert forall t :: 0 <= t < |a| - i ==> b[j] < a[i+t] || t == 0;
        assert b[j] < a[i]; // from branch condition a[i] > b[j]
      } else {
        assert b[j] <= b[j+1];
        assert b[j] < a[i];
      }
      assert forall t :: 0 <= t < |b| - (j+1) ==> b[j] <= b[j+1+t] by { }
      assert forall t :: 0 <= t < |a| - i ==> b[j] <= a[i+t] by {
        assert b[j] < a[i];
      }
    }
    assert Sorted([b[j]] + mergeModel(a,b,i,j+1));
  }
}

lemma MergeModelMultiset(a: seq<int>, b: seq<int>, i: nat, j: nat)
  requires i <= |a| && j <= |b|
  requires Sorted(a) && Sorted(b)
  ensures multisetOf(mergeModel(a,b,i,j)) == multisetOf(a[i..]) + multisetOf(b[j..])
  decreases (|a| - i) + (|b| - j)
{
  if i == |a| {
  } else if j == |b| {
  } else if a[i] <= b[j] {
    MergeModelMultiset(a,b,i+1,j);
    calc {
      multisetOf(mergeModel(a,b,i,j));
      == { }
      multisetOf([a[i]] + mergeModel(a,b,i+1,j));
      == { }
      multisetOf([a[i]]) + multisetOf(mergeModel(a,b,i+1,j));
      == { }
      multisetOf([a[i]]) + (multisetOf(a[i+1..]) + multisetOf(b[j..]));
      == { assert a[i..] == [a[i]] + a[i+1..]; }
      multisetOf(a[i..]) + multisetOf(b[j..]);
    }
  } else {
    MergeModelMultiset(a,b,i,j+1);
    calc {
      multisetOf(mergeModel(a,b,i,j));
      == { }
      multisetOf([b[j]] + mergeModel(a,b,i,j+1));
      == { }
      multisetOf([b[j]]) + multisetOf(mergeModel(a,b,i,j+1));
      == { }
      multisetOf([b[j]]) + (multisetOf(a[i..]) + multisetOf(b[j+1..]));
      == { assert b[j..] == [b[j]] + b[j+1..]; }
      multisetOf(a[i..]) + multisetOf(b[j..]);
    }
  }
}

// Order-preserving merge of two sorted sequences (defined via mergeModel for easier proofs)
ghost function mergeSeq(a: seq<int>, b: seq<int>): seq<int>
  requires Sorted(a)
  requires Sorted(b)
  ensures |mergeSeq(a,b)| == |a| + |b|
  ensures Sorted(mergeSeq(a,b))
  ensures multisetOf(mergeSeq(a,b)) == multisetOf(a) + multisetOf(b)
{
  mergeModel(a,b,0,0)
}

// Connect mergeModel at (0,0) with mergeSeq (now definitional)
lemma MergeModelIsMergeSeq(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures mergeModel(a,b,0,0) == mergeSeq(a,b)
{
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

    // establish loop invariant on entry: prefix length is 0 on both sides
    assert c[..0] == mergeModel(a[..], b[..], 0, 0)[..0];

    while i < a.Length || j < b.Length
      decreases (a.Length - i) + (b.Length - j)
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant i + j <= c.Length
      invariant c[..i+j] == mergeModel(a[..], b[..], i as nat, j as nat)[..i+j]
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            i := i + 1;

            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;

            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
        }
    }

    assert !(i < a.Length || j < b.Length);
    assert i == a.Length && j == b.Length;
    assert c[..] == c[..c.Length];

    // Now the invariant gives full equality (both sides have full length)
    assert c[..] == mergeModel(a[..], b[..], a.Length as nat, b.Length as nat)[..c.Length];
    assert mergeModel(a[..], b[..], a.Length as nat, b.Length as nat) == [];
    assert mergeModel(a[..], b[..], a.Length as nat, b.Length as nat)[..c.Length] == mergeModel(a[..], b[..], 0, 0);
    assert c[..] == mergeModel(a[..], b[..], 0, 0);

    MergeModelSorted(a[..], b[..], 0, 0);
    MergeModelMultiset(a[..], b[..], 0, 0);
    assert Sorted(c[..]);
    assert multisetOf(c[..]) == multisetOf(a[..]) + multisetOf(b[..]);

    MergeModelIsMergeSeq(a[..], b[..]);
    assert c[..] == mergeSeq(a[..], b[..]);
}

// Test case checked statically
method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);
    assert c[..] == [1, 2, 3, 4, 5];
}

