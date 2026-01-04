// Auxiliary predicates
predicate IsEven(n: int) {
  n % 2 == 0
}
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Ghost predicates capturing “is the first even/odd index”
ghost predicate IsFirstEvenIndex(a: array<int>, i: int)
  requires a.Length > 0
  reads a
{
  0 <= i < a.Length &&
  IsEven(a[i]) &&
  (forall k :: 0 <= k < i ==> !IsEven(a[k]))
}

ghost predicate IsFirstOddIndex(a: array<int>, i: int)
  requires a.Length > 0
  reads a
{
  0 <= i < a.Length &&
  IsOdd(a[i]) &&
  (forall k :: 0 <= k < i ==> !IsOdd(a[k]))
}

// Lemmas: from existence of any even/odd, we can construct a "first" index
lemma ExistsEvenImpliesExistsFirstEven(a: array<int>)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  ensures exists i :: IsFirstEvenIndex(a, i)
  reads a
{
  var e :| 0 <= e < a.Length && IsEven(a[e]);

  // Choose the minimal even index via a set of candidates and "min"
  var S := set i | 0 <= i < a.Length && IsEven(a[i]);
  assert e in S;
  assert S != {};
  var m :| m in S && forall j :: j in S ==> m <= j;

  assert 0 <= m < a.Length;
  assert IsEven(a[m]);

  // show no earlier even exists
  assert forall k :: 0 <= k < m ==> !IsEven(a[k]) by {
    forall k | 0 <= k < m
      ensures !IsEven(a[k])
    {
      if IsEven(a[k]) {
        assert k in S;
        assert m <= k;
        assert k < m;
      }
    }
  }

  assert IsFirstEvenIndex(a, m);
}

lemma ExistsOddImpliesExistsFirstOdd(a: array<int>)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures exists i :: IsFirstOddIndex(a, i)
  reads a
{
  var o :| 0 <= o < a.Length && IsOdd(a[o]);

  var S := set i | 0 <= i < a.Length && IsOdd(a[i]);
  assert o in S;
  assert S != {};
  var m :| m in S && forall j :: j in S ==> m <= j;

  assert 0 <= m < a.Length;
  assert IsOdd(a[m]);

  assert forall k :: 0 <= k < m ==> !IsOdd(a[k]) by {
    forall k | 0 <= k < m
      ensures !IsOdd(a[k])
    {
      if IsOdd(a[k]) {
        assert k in S;
        assert m <= k;
        assert k < m;
      }
    }
  }

  assert IsFirstOddIndex(a, m);
}

// Ghost functions to define "first index" precisely in specifications
ghost function FirstEvenIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: IsFirstEvenIndex(a, i)
  reads a
  ensures IsFirstEvenIndex(a, FirstEvenIndex(a))
{
  var fe :| IsFirstEvenIndex(a, fe);
  fe
}

ghost function FirstOddIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: IsFirstOddIndex(a, i)
  reads a
  ensures IsFirstOddIndex(a, FirstOddIndex(a))
{
  var fo :| IsFirstOddIndex(a, fo);
  fo
}

// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures diff == a[FirstEvenIndex(a)] - a[FirstOddIndex(a)]
{
  // establish the additional existence facts needed to call FirstEvenIndex/FirstOddIndex in the postcondition
  ExistsEvenImpliesExistsFirstEven(a);
  ExistsOddImpliesExistsFirstOdd(a);

  var firstEven := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= firstEven < a.Length
    // if we haven't found one yet, all seen are not even
    invariant firstEven == 0 ==> (forall j :: 0 <= j < i ==> !IsEven(a[j]))
    // if we have found one, it is even and is the first even
    invariant firstEven != 0 ==> IsEven(a[firstEven]) && (forall j :: 0 <= j < firstEven ==> !IsEven(a[j]))
  {
    if IsEven(a[i]) {
      firstEven := i;
      break;
    }
  }

  // establish that the chosen firstEven satisfies the "first even" characterization,
  // including the important case firstEven==0 (then a[0] is even)
  assert 0 <= firstEven < a.Length;
  if firstEven == 0 {
    assert IsEven(a[0]);
  }
  assert IsEven(a[firstEven]);
  assert forall j :: 0 <= j < firstEven ==> !IsEven(a[j]);

  var firstOdd := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= firstOdd < a.Length
    invariant firstOdd == 0 ==> (forall j :: 0 <= j < i ==> !IsOdd(a[j]))
    invariant firstOdd != 0 ==> IsOdd(a[firstOdd]) && (forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]))
  {
    if IsOdd(a[i]) {
      firstOdd := i;
      break;
    }
  }

  assert 0 <= firstOdd < a.Length;
  if firstOdd == 0 {
    assert IsOdd(a[0]);
  }
  assert IsOdd(a[firstOdd]);
  assert forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]);

  return a[firstEven] - a[firstOdd];
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest() {
  var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
  assert a1[..] == [1, 3, 5, 7, 4, 1, 6, 8];
  // concrete witnesses for preconditions
  assert IsEven(a1[4]);
  assert IsOdd(a1[0]);
  assert exists i :: 0 <= i < a1.Length && IsEven(a1[i]);
  assert exists i :: 0 <= i < a1.Length && IsOdd(a1[i]);
  var out1 := FirstEvenOddDifference(a1);
  assert out1 == 3;

  var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  assert a2[..] == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  assert IsEven(a2[1]);
  assert IsOdd(a2[0]);
  assert exists i :: 0 <= i < a2.Length && IsEven(a2[i]);
  assert exists i :: 0 <= i < a2.Length && IsOdd(a2[i]);
  var out2 := FirstEvenOddDifference(a2);
  assert out2 == 1;

  var a3 := new int[] [1, 5, 7, 9, 10];
  assert a3[..] == [1, 5, 7, 9, 10];
  assert IsEven(a3[4]);
  assert IsOdd(a3[0]);
  assert exists i :: 0 <= i < a3.Length && IsEven(a3[i]);
  assert exists i :: 0 <= i < a3.Length && IsOdd(a3[i]);
  var out3 := FirstEvenOddDifference(a3);
  assert out3 == 9;
}
