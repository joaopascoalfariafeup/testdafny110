// Returns the difference between the first even and the first odd number in the array.

function FirstEvenIndex(s: seq<int>): int
  requires exists k :: 0 <= k < |s| && IsEven(s[k])
  ensures 0 <= FirstEvenIndex(s) < |s|
  ensures IsEven(s[FirstEvenIndex(s)])
  ensures forall j :: 0 <= j < FirstEvenIndex(s) ==> !IsEven(s[j])
  decreases |s|
{
  if IsEven(s[0]) then 0 else 1 + FirstEvenIndex(s[1..])
}

function FirstOddIndex(s: seq<int>): int
  requires exists k :: 0 <= k < |s| && IsOdd(s[k])
  ensures 0 <= FirstOddIndex(s) < |s|
  ensures IsOdd(s[FirstOddIndex(s)])
  ensures forall j :: 0 <= j < FirstOddIndex(s) ==> !IsOdd(s[j])
  decreases |s|
{
  if IsOdd(s[0]) then 0 else 1 + FirstOddIndex(s[1..])
}

lemma FirstEvenIndexUnique(s: seq<int>, i: int)
  requires exists k :: 0 <= k < |s| && IsEven(s[k])
  requires 0 <= i < |s|
  requires IsEven(s[i])
  requires forall j :: 0 <= j < i ==> !IsEven(s[j])
  ensures FirstEvenIndex(s) == i
{
  var r := FirstEvenIndex(s);
  if r < i {
    assert 0 <= r < i;
    assert !IsEven(s[r]);
    assert IsEven(s[r]);
  }
  if r > i {
    assert 0 <= i < r;
    assert !IsEven(s[i]);
    assert IsEven(s[i]);
  }
}

lemma FirstOddIndexUnique(s: seq<int>, i: int)
  requires exists k :: 0 <= k < |s| && IsOdd(s[k])
  requires 0 <= i < |s|
  requires IsOdd(s[i])
  requires forall j :: 0 <= j < i ==> !IsOdd(s[j])
  ensures FirstOddIndex(s) == i
{
  var r := FirstOddIndex(s);
  if r < i {
    assert 0 <= r < i;
    assert !IsOdd(s[r]);
    assert IsOdd(s[r]);
  }
  if r > i {
    assert 0 <= i < r;
    assert !IsOdd(s[i]);
    assert IsOdd(s[i]);
  }
}

method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires exists k :: 0 <= k < a.Length && IsEven(a[k])
  requires exists k :: 0 <= k < a.Length && IsOdd(a[k])
  ensures diff == a[FirstEvenIndex(a[..])] - a[FirstOddIndex(a[..])]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsEven(a[j])
      invariant exists k :: i <= k < a.Length && IsEven(a[k])
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
        assert !IsEven(a[i]);
    }
    assert 0 <= firstEven < a.Length;
    assert IsEven(a[firstEven]);
    assert forall j :: 0 <= j < firstEven ==> !IsEven(a[j]);
    assert firstEven == FirstEvenIndex(a[..]) by {
      FirstEvenIndexUnique(a[..], firstEven);
    }

    var firstOdd: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
      invariant exists k :: i <= k < a.Length && IsOdd(a[k])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            break;
        }
        assert !IsOdd(a[i]);
    }
    assert 0 <= firstOdd < a.Length;
    assert IsOdd(a[firstOdd]);
    assert forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]);
    assert firstOdd == FirstOddIndex(a[..]) by {
      FirstOddIndexUnique(a[..], firstOdd);
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
