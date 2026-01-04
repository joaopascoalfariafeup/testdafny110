// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures diff == a[MinEvenIndex(a)] - a[MinOddIndex(a)]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant exists j :: 0 <= j < a.Length && IsEven(a[j])
      invariant 0 <= i <= a.Length
      invariant i == 0 ==> firstEven == 0
      invariant 0 <= firstEven < a.Length
      invariant (forall k :: 0 <= k < i ==> !IsEven(a[k])) ==> firstEven == 0
      invariant firstEven != 0 ==> IsEven(a[firstEven])
      invariant firstEven != 0 ==> (forall k :: 0 <= k < firstEven ==> !IsEven(a[k]))
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }

    assert 0 <= firstEven < a.Length;
    assert IsEven(a[firstEven]);
    assert forall k :: 0 <= k < firstEven ==> !IsEven(a[k]);

    var firstOdd: int;
    for i := 0 to a.Length
      invariant exists j :: 0 <= j < a.Length && IsOdd(a[j])
      invariant 0 <= i <= a.Length
      invariant i == 0 ==> firstOdd == 0
      invariant 0 <= firstOdd < a.Length
      invariant (forall k :: 0 <= k < i ==> !IsOdd(a[k])) ==> firstOdd == 0
      invariant firstOdd != 0 ==> IsOdd(a[firstOdd])
      invariant firstOdd != 0 ==> (forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k]))
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            break;
        }
    }

    assert 0 <= firstOdd < a.Length;
    assert IsOdd(a[firstOdd]);
    assert forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k]);

    assert firstEven == MinEvenIndex(a);
    assert firstOdd == MinOddIndex(a);

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

function MinEvenIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
{
  var m :| 0 <= m < a.Length && IsEven(a[m]) && (forall k :: 0 <= k < m ==> !IsEven(a[k]));
  m
}

function MinOddIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
{
  var m :| 0 <= m < a.Length && IsOdd(a[m]) && (forall k :: 0 <= k < m ==> !IsOdd(a[k]));
  m
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
