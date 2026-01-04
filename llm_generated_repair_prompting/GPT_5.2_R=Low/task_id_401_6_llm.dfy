// Helper lemma: sequence extensionality
lemma SeqEq<T>(s: seq<T>, t: seq<T>)
  requires |s| == |t|
  requires forall i:int :: 0 <= i < |s| ==> s[i] == t[i]
  ensures s == t
{
  assert s == t;
}

// Helper lemma: extending a sequence-comprehension by one element
lemma SeqExtend<T>(n: int, f: int -> T)
  requires n >= 0
  ensures seq(n + 1, i requires 0 <= i < n + 1 => f(i))
        == seq(n,     i requires 0 <= i < n     => f(i)) + [f(n)]
{
  var left := seq(n + 1, i requires 0 <= i < n + 1 => f(i));
  var prefix := seq(n, j requires 0 <= j < n => f(j));
  var right := prefix + [f(n)];

  assert |left| == n + 1;
  assert |prefix| == n;
  assert |right| == n + 1;

  // Pointwise equality
  forall i:int | 0 <= i < |left|
    ensures left[i] == right[i]
  {
    if i < n {
      // right[i] comes from the prefix
      assert right[i] == prefix[i];
      assert prefix[i] == f(i);
      assert left[i] == f(i);
    } else {
      assert i == n;
      // right[n] is the appended element
      assert right[i] == f(n);
      assert left[i] == f(n);
    }
  }

  SeqEq(left, right);
}

function EWAdd(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  seq(|a|, i requires 0 <= i < |a| => a[i] + b[i])
}

function DeepEWAdd(a: seq<seq<int>>, b: seq<seq<int>>): seq<seq<int>>
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
{
  seq(|a|, i requires 0 <= i < |a| => EWAdd(a[i], b[i]))
}

method DeepElementWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  ensures result == DeepEWAdd(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant result == seq(i, k requires 0 <= k < i => EWAdd(a[k], b[k]))
  {
    assert i < |a|;

    var subResult := ElementWiseAddition(a[i], b[i]);
    assert subResult == EWAdd(a[i], b[i]);

    // Help Dafny re-establish the seq-comprehension invariant after appending.
    // NOTE: the lambda passed to SeqExtend must be total, so we guard the indexing.
    assert seq(i + 1, k requires 0 <= k < i + 1 => EWAdd(a[k], b[k]))
         == seq(i,     k requires 0 <= k < i     => EWAdd(a[k], b[k])) + [EWAdd(a[i], b[i])]
      by {
        SeqExtend(i, k => if 0 <= k < |a| then EWAdd(a[k], b[k]) else []);
      }

    result := result + [subResult];
  }
}


// Auxiliary method to compute the element wise addition of two sequences of equal size.
method ElementWiseAddition(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  ensures result == EWAdd(a, b)
{
  result := [];
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant result == seq(i, k requires 0 <= k < i => a[k] + b[k])
  {
      assert i < |a|;

      // Help Dafny re-establish the seq-comprehension invariant after appending.
      // NOTE: the lambda passed to SeqExtend must be total, so we guard the indexing.
      assert seq(i + 1, k requires 0 <= k < i + 1 => a[k] + b[k])
           == seq(i,     k requires 0 <= k < i     => a[k] + b[k]) + [a[i] + b[i]]
        by { SeqExtend(i, k => if 0 <= k < |a| then a[k] + b[k] else 0); }

      result := result + [a[i] + b[i]];
  }
}

// Test cases checked statically
method IndexWiseAdditionTest(){
  var s1:seq<seq<int>> :=[[4], [1, 3], [2, 9, 1], []];
  var s2:seq<seq<int>> :=[[2], [6, 7], [1, 1, 8], []];
  var res1 := DeepElementWiseAddition(s1,s2);

  // Proof helpers for the expected concrete result
  assert EWAdd([4], [2]) == [6];
  assert EWAdd([1, 3], [6, 7]) == [7, 10];
  assert EWAdd([2, 9, 1], [1, 1, 8]) == [3, 10, 9];
  assert EWAdd([], []) == [];

  assert DeepEWAdd(s1, s2) == [[6], [7, 10], [3, 10, 9], []];

  // now the full assertion
  assert res1 == [[6], [7, 10], [3, 10, 9], []];
}

