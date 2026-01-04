// Auxiliary predicates
predicate IsEven(n: int) {
  n % 2 == 0
}
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Ghost functions to define "first index" precisely in specifications
ghost function FirstEvenIndex(a: array<int>): int
  requires a != null
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  ensures 0 <= FirstEvenIndex(a) < a.Length
  ensures IsEven(a[FirstEvenIndex(a)])
  ensures forall j :: 0 <= j < FirstEvenIndex(a) ==> !IsEven(a[j])
{
  var fe :| 0 <= fe < a.Length &&
            IsEven(a[fe]) &&
            (forall j :: 0 <= j < fe ==> !IsEven(a[j]));
  fe
}

ghost function FirstOddIndex(a: array<int>): int
  requires a != null
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures 0 <= FirstOddIndex(a) < a.Length
  ensures IsOdd(a[FirstOddIndex(a)])
  ensures forall j :: 0 <= j < FirstOddIndex(a) ==> !IsOdd(a[j])
{
  var fo :| 0 <= fo < a.Length &&
            IsOdd(a[fo]) &&
            (forall j :: 0 <= j < fo ==> !IsOdd(a[j]));
  fo
}

// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a != null
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures diff == a[FirstEvenIndex(a)] - a[FirstOddIndex(a)]
{
  var firstEven := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= firstEven < a.Length
    invariant firstEven == 0 ==> (forall j :: 0 <= j < i ==> !IsEven(a[j]))
    invariant firstEven != 0 ==> IsEven(a[firstEven]) && (forall j :: 0 <= j < firstEven ==> !IsEven(a[j]))
    decreases a.Length - i
  {
    if IsEven(a[i]) {
      firstEven := i;
      break;
    }
  }

  assert 0 <= firstEven < a.Length;
  assert IsEven(a[firstEven]);
  assert forall j :: 0 <= j < firstEven ==> !IsEven(a[j]);

  var firstOdd := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= firstOdd < a.Length
    invariant firstOdd == 0 ==> (forall j :: 0 <= j < i ==> !IsOdd(a[j]))
    invariant firstOdd != 0 ==> IsOdd(a[firstOdd]) && (forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]))
    decreases a.Length - i
  {
    if IsOdd(a[i]) {
      firstOdd := i;
      break;
    }
  }

  assert 0 <= firstOdd < a.Length;
  assert IsOdd(a[firstOdd]);
  assert forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]);

  return a[firstEven] - a[firstOdd];
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest() {
  var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
  assert a1[..] == [1, 3, 5, 7, 4, 1, 6, 8];
  var out1 := FirstEvenOddDifference(a1);
  assert out1 == 3;

  var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  assert a2[..] == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  var out2 := FirstEvenOddDifference(a2);
  assert out2 == 1;

  var a3 := new int[] [1, 5, 7, 9, 10];
  assert a3[..] == [1, 5, 7, 9, 10];
  var out3 := FirstEvenOddDifference(a3);
  assert out3 == 9;
}
