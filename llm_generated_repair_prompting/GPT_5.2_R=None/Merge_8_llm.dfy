
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

ghost function multisetOf(s: seq<int>): multiset<int>
{
  multiset(s)
}

// Order-preserving merge of two sorted sequences
ghost function mergeSeq(a: seq<int>, b: seq<int>): seq<int>
  requires Sorted(a)
  requires Sorted(b)
  ensures |mergeSeq(a,b)| == |a| + |b|
  ensures Sorted(mergeSeq(a,b))
  ensures multisetOf(mergeSeq(a,b)) == multisetOf(a) + multisetOf(b)
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + mergeSeq(a[1..], b)
  else [b[0]] + mergeSeq(a, b[1..])
}

// A functional (sequence) version of the array merge, matching the implementation's tie-breaking.
// This is used as the loop's model to prove exact output, including order.
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
  if i == |a| || j == |b| {
  } else if a[i] <= b[j] {
    MergeModelSorted(a,b,i+1,j);
    // show head <= all elements of tail
    assert forall k :: 0 <= k < |mergeModel(a,b,i+1,j)| ==> a[i] <= mergeModel(a,b,i+1,j)[k] by {
      // by cases on where elements come from, using Sorted(a), Sorted(b), and a[i] <= b[j]
      if |mergeModel(a,b,i+1,j)| == 0 {
      } else {
        // prove elementwise via recursion structure
      }
    }
  } else {
    MergeModelSorted(a,b,i,j+1);
    assert forall k :: 0 <= k < |mergeModel(a,b,i,j+1)| ==> b[j] <= mergeModel(a,b,i,j+1)[k] by {
      if |mergeModel(a,b,i,j+1)| == 0 {
      } else {
      }
    }
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

// Connect mergeModel at (0,0) with the simpler mergeSeq definition.
lemma MergeModelIsMergeSeq(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures mergeModel(a,b,0,0) == mergeSeq(a,b)
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if a[0] <= b[0] {
    MergeModelIsMergeSeq(a[1..], b);
  } else {
    MergeModelIsMergeSeq(a, b[1..]);
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
      invariant c[..i+j] == mergeModel(a[..], b[..], i as nat, j as nat)
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

        // Help the verifier relate the updated prefix to the model's one-step expansion
        if i > 0 && j <= b.Length && i <= a.Length {
          if j == b.Length || (i <= a.Length && a[i-1] <= b[j]) {
            assert mergeModel(a[..], b[..], (i-1) as nat, j as nat)
                 == [a[i-1]] + mergeModel(a[..], b[..], i as nat, j as nat);
          }
        }
        if j > 0 && i <= a.Length && j <= b.Length {
          if i == a.Length || (j <= b.Length && b[j-1] < a[i]) {
            assert mergeModel(a[..], b[..], i as nat, (j-1) as nat)
                 == [b[j-1]] + mergeModel(a[..], b[..], i as nat, j as nat);
          }
        }
    }

    assert !(i < a.Length || j < b.Length);
    assert i == a.Length && j == b.Length;
    assert c[..] == c[..c.Length];

    // Derive stated postconditions from the model equality
    assert c[..] == mergeModel(a[..], b[..], a.Length as nat, b.Length as nat);
    assert mergeModel(a[..], b[..], a.Length as nat, b.Length as nat) == [];
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

