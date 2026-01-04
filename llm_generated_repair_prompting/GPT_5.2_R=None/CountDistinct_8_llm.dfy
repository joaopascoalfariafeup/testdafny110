
// Helper predicate to avoid brittle quantifier triggers in loop invariants
ghost predicate IsChangeAt(a: array<int>, j: int)
  reads a
{
  1 <= j < a.Length && a[j] != a[j-1]
}

// Small lemma to relate the set-of-changes cardinality at i vs i-1
lemma ChangesUpToStep(a: array<int>, i: int)
  requires 2 <= i <= a.Length
  ensures |set j | 1 <= j < i && IsChangeAt(a, j)|
        == |set j | 1 <= j < i-1 && IsChangeAt(a, j)| + (if IsChangeAt(a, i-1) then 1 else 0)
{
  var S := set j | 1 <= j < i-1 && IsChangeAt(a, j);
  var T := set j | 1 <= j < i && IsChangeAt(a, j);

  assert T == S + (if IsChangeAt(a, i-1) then {i-1} else {});
  if IsChangeAt(a, i-1) {
    assert i-1 !in S;
    assert |S + {i-1}| == |S| + 1;
  } else {
    assert (if IsChangeAt(a, i-1) then {i-1} else {}) == {};
    assert S + {} == S;
  }
}

// A ghost “count changes” function that matches the loop direction (from left to right).
ghost function ChangesUpTo(a: array<int>, i: int): nat
  requires 1 <= i <= a.Length
  reads a
  decreases i
  ensures ChangesUpTo(a, i) == |set j | 1 <= j < i && IsChangeAt(a, j)|
{
  if i == 1 then
    0
  else
    (ChangesUpToStep(a, i);
     ChangesUpTo(a, i - 1) + (if IsChangeAt(a, i - 1) then 1 else 0))
}

// Returns the number of distinct elements in a sorted array of integers.
method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
  ensures count <= a.Length
  ensures a.Length == 0 ==> count == 0
  ensures a.Length > 0 ==> count >= 1
  ensures count ==
    if a.Length == 0 then 0
    else 1 + ChangesUpTo(a, a.Length)
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= count <= i
      invariant count == 1 + ChangesUpTo(a, i)
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
}

method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    assert a[..] == [1, 1, 2, 2, 3];
    // help the precondition (sorted)
    assert forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1];

    var count := CountDistinct(a);

    // Help Dafny connect the concrete array with ChangesUpTo/set reasoning
    assert IsChangeAt(a, 2);
    assert IsChangeAt(a, 4);
    assert !IsChangeAt(a, 1);
    assert !IsChangeAt(a, 3);

    // Fix: parenthesize the set comprehension; otherwise "&&" is parsed inside it
    assert (set j | 1 <= j < a.Length && IsChangeAt(a, j)) == {2, 4};
    assert |set j | 1 <= j < a.Length && IsChangeAt(a, j)| == 2;

    assert ChangesUpTo(a, a.Length) == 2;
    assert count == 3;
}

