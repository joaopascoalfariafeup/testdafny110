// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures diff == a[FirstEvenIndex(a[..])] - a[FirstOddIndex(a[..])]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= firstEven < a.Length
      invariant IsEven(a[firstEven]) ==> (firstEven <= i && IsFirstEvenIndex(a[..], firstEven))
      invariant !IsEven(a[firstEven]) ==> (forall j :: 0 <= j < i ==> !IsEven(a[j]))
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }

    ghost {
      assert IsEven(a[firstEven]);
      assert IsFirstEvenIndex(a[..], firstEven);
      FirstEvenIndexUnique(a[..], firstEven);
      assert firstEven == FirstEvenIndex(a[..]);
    }

    var firstOdd: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= firstOdd < a.Length
      invariant IsOdd(a[firstOdd]) ==> (firstOdd <= i && IsFirstOddIndex(a[..], firstOdd))
      invariant !IsOdd(a[firstOdd]) ==> (forall j :: 0 <= j < i ==> !IsOdd(a[j]))
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            break;
        }
    }

    ghost {
      assert IsOdd(a[firstOdd]);
      assert IsFirstOddIndex(a[..], firstOdd);
      FirstOddIndexUnique(a[..], firstOdd);
      assert firstOdd == FirstOddIndex(a[..]);
    }

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

predicate IsFirstEvenIndex(s: seq<int>, idx: int)
{
  0 <= idx < |s| &&
  IsEven(s[idx]) &&
  (forall j :: 0 <= j < idx ==> !IsEven(s[j]))
}

predicate IsFirstOddIndex(s: seq<int>, idx: int)
{
  0 <= idx < |s| &&
  IsOdd(s[idx]) &&
  (forall j :: 0 <= j < idx ==> !IsOdd(s[j]))
}

function {:fuel 20} FirstEvenIndex(s: seq<int>): int
  requires exists i :: 0 <= i < |s| && IsEven(s[i])
  decreases |s|
{
  if IsEven(s[0]) then 0 else 1 + FirstEvenIndex(s[1..])
}

function {:fuel 20} FirstOddIndex(s: seq<int>): int
  requires exists i :: 0 <= i < |s| && IsOdd(s[i])
  decreases |s|
{
  if IsOdd(s[0]) then 0 else 1 + FirstOddIndex(s[1..])
}

lemma FirstEvenIndexUnique(s: seq<int>, idx: int)
  requires exists i :: 0 <= i < |s| && IsEven(s[i])
  requires IsFirstEvenIndex(s, idx)
  ensures idx == FirstEvenIndex(s)
  decreases |s|
{
  if IsEven(s[0]) {
  } else {
    assert idx != 0;
    assert 1 <= idx < |s|;
    assert IsEven(s[idx]);
    assert forall j :: 0 <= j < idx ==> !IsEven(s[j]);
    assert IsEven(s[1..][idx - 1]);
    assert forall j :: 0 <= j < idx - 1 ==> !IsEven(s[1..][j]);
    assert IsFirstEvenIndex(s[1..], idx - 1);
    assert exists i :: 0 <= i < |s[1..]| && IsEven(s[1..][i]);
    FirstEvenIndexUnique(s[1..], idx - 1);
  }
}

lemma FirstOddIndexUnique(s: seq<int>, idx: int)
  requires exists i :: 0 <= i < |s| && IsOdd(s[i])
  requires IsFirstOddIndex(s, idx)
  ensures idx == FirstOddIndex(s)
  decreases |s|
{
  if IsOdd(s[0]) {
  } else {
    assert idx != 0;
    assert 1 <= idx < |s|;
    assert IsOdd(s[idx]);
    assert forall j :: 0 <= j < idx ==> !IsOdd(s[j]);
    assert IsOdd(s[1..][idx - 1]);
    assert forall j :: 0 <= j < idx - 1 ==> !IsOdd(s[1..][j]);
    assert IsFirstOddIndex(s[1..], idx - 1);
    assert exists i :: 0 <= i < |s[1..]| && IsOdd(s[1..][i]);
    FirstOddIndexUnique(s[1..], idx - 1);
  }
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest(){
    var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
    var out1 := FirstEvenOddDifference(a1);
    assert out1 == 3;

    var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    var out2 := FirstEvenOddDifference(a2);
    assert out2 == 1;

    var a3:= new int[] [1, 5, 7, 9, 10];
    var out3 := FirstEvenOddDifference(a3);
    assert out3 == 9;
}
