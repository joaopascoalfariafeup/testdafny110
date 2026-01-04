
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

lemma MultisetSingleton<T>(x: T)
  ensures multiset([x]) == multiset{} + multiset{x}
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
      invariant Sorted(c[..i+j])
      invariant forall x :: 0 <= x < i ==> (j < b.Length ==> a[x] <= b[j])
      invariant forall y :: 0 <= y < j ==> (i < a.Length ==> b[y] <= a[i])
      invariant c[..i+j] == mergeSeq(a[..i], b[..j])
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];
            i := i + 1;

            // Help the verifier update the multiset invariant after writing c[i+j-1]
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
            calc {
              multisetOf(c[..i+j]);
              == { }
              multiset(c[..i+j]);
              == { assert c[..i+j] == c[..i+j-1] + [c[i+j-1]]; }
              multiset(c[..i+j-1] + [c[i+j-1]]);
              == { MultisetOfConcat(c[..i+j-1], [c[i+j-1]]) }
              multiset(c[..i+j-1]) + multiset([c[i+j-1]]);
              == { }
              multisetOf(c[..i+j-1]) + multisetOf([c[i+j-1]]);
            }
            assert c[i+j-1] == a[i-1];
            assert a[..i] == a[..i-1] + [a[i-1]];
            calc {
              multisetOf(a[..i]);
              == { assert a[..i] == a[..i-1] + [a[i-1]]; }
              multiset(a[..i-1] + [a[i-1]]);
              == { MultisetOfConcat(a[..i-1], [a[i-1]]) }
              multiset(a[..i-1]) + multiset([a[i-1]]);
              == { }
              multisetOf(a[..i-1]) + multisetOf([a[i-1]]);
            }
        } 
        else {
            c[i + j] := b[j];
            j := j + 1;

            // Help the verifier update the multiset invariant after writing c[i+j-1]
            assert c[..i+j] == c[..i+j-1] + [c[i+j-1]];
            calc {
              multisetOf(c[..i+j]);
              == { }
              multiset(c[..i+j]);
              == { assert c[..i+j] == c[..i+j-1] + [c[i+j-1]]; }
              multiset(c[..i+j-1] + [c[i+j-1]]);
              == { MultisetOfConcat(c[..i+j-1], [c[i+j-1]]) }
              multiset(c[..i+j-1]) + multiset([c[i+j-1]]);
              == { }
              multisetOf(c[..i+j-1]) + multisetOf([c[i+j-1]]);
            }
            assert c[i+j-1] == b[j-1];
            assert b[..j] == b[..j-1] + [b[j-1]];
            calc {
              multisetOf(b[..j]);
              == { assert b[..j] == b[..j-1] + [b[j-1]]; }
              multiset(b[..j-1] + [b[j-1]]);
              == { MultisetOfConcat(b[..j-1], [b[j-1]]) }
              multiset(b[..j-1]) + multiset([b[j-1]]);
              == { }
              multisetOf(b[..j-1]) + multisetOf([b[j-1]]);
            }
        }
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

