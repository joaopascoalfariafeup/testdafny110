// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a != null
  requires exists k :: 0 <= k < a.Length && IsEven(a[k])
  requires exists k :: 0 <= k < a.Length && IsOdd(a[k])
  ensures diff == a[FirstEvenIndex(a[..])] - a[FirstOddIndex(a[..])]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsEven(a[j])
    {
        if IsEven(a[i]) {
            firstEven := i;
            assert FirstEvenAt(a[..], firstEven);
            // Uniqueness: the first-even position is uniquely determined
            FirstEvenUnique(a[..], firstEven, FirstEvenIndex(a[..]));
            assert firstEven == FirstEvenIndex(a[..]);
            break;
        }
    }

    var firstOdd: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            assert FirstOddAt(a[..], firstOdd);
            // Uniqueness: the first-odd position is uniquely determined
            FirstOddUnique(a[..], firstOdd, FirstOddIndex(a[..]));
            assert firstOdd == FirstOddIndex(a[..]);
            break;
        }
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

predicate FirstEvenAt(s: seq<int>, i: int)
{
  0 <= i < |s| &&
  IsEven(s[i]) &&
  (forall j :: 0 <= j < i ==> !IsEven(s[j]))
}

predicate FirstOddAt(s: seq<int>, i: int)
{
  0 <= i < |s| &&
  IsOdd(s[i]) &&
  (forall j :: 0 <= j < i ==> !IsOdd(s[j]))
}

lemma FirstEvenUnique(s: seq<int>, i: int, j: int)
  requires FirstEvenAt(s, i)
  requires FirstEvenAt(s, j)
  ensures i == j
{
  if i < j {
    assert !IsEven(s[j]);
  } else if j < i {
    assert !IsEven(s[i]);
  }
}

lemma FirstOddUnique(s: seq<int>, i: int, j: int)
  requires FirstOddAt(s, i)
  requires FirstOddAt(s, j)
  ensures i == j
{
  if i < j {
    assert !IsOdd(s[j]);
  } else if j < i {
    assert !IsOdd(s[i]);
  }
}

function {:fuel 20} FirstEvenIndex(s: seq<int>): nat
  requires exists k :: 0 <= k < |s| && IsEven(s[k])
  ensures FirstEvenAt(s, FirstEvenIndex(s))
{
  if IsEven(s[0]) then 0 else 1 + FirstEvenIndex(s[1..])
}

function {:fuel 20} FirstOddIndex(s: seq<int>): nat
  requires exists k :: 0 <= k < |s| && IsOdd(s[k])
  ensures FirstOddAt(s, FirstOddIndex(s))
{
  if IsOdd(s[0]) then 0 else 1 + FirstOddIndex(s[1..])
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest(){
    var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
    assert a1[..] == [1, 3, 5, 7, 4, 1, 6, 8];
    assert IsOdd(a1[0]) && IsEven(a1[4]);
    assert exists k :: 0 <= k < a1.Length && IsOdd(a1[k]);
    assert exists k :: 0 <= k < a1.Length && IsEven(a1[k]);
    assert FirstOddIndex(a1[..]) == 0;
    assert FirstEvenIndex(a1[..]) == 4;
    var out1 := FirstEvenOddDifference(a1);
    assert out1 == 3;

    var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    assert a2[..] == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    assert IsOdd(a2[0]) && IsEven(a2[1]);
    assert exists k :: 0 <= k < a2.Length && IsOdd(a2[k]);
    assert exists k :: 0 <= k < a2.Length && IsEven(a2[k]);
    assert FirstOddIndex(a2[..]) == 0;
    assert FirstEvenIndex(a2[..]) == 1;
    var out2 := FirstEvenOddDifference(a2);
    assert out2 == 1;

    var a3:= new int[] [1, 5, 7, 9, 10];
    assert a3[..] == [1, 5, 7, 9, 10];
    assert IsOdd(a3[0]) && IsEven(a3[4]);
    assert exists k :: 0 <= k < a3.Length && IsOdd(a3[k]);
    assert exists k :: 0 <= k < a3.Length && IsEven(a3[k]);
    assert FirstOddIndex(a3[..]) == 0;
    assert FirstEvenIndex(a3[..]) == 4;
    var out3 := FirstEvenOddDifference(a3);
    assert out3 == 9;
}
