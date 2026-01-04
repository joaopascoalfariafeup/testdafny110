// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i]) // There is at least one even number
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])  // There is at least one odd number
  ensures diff == a[FirstEvenIndex(a)] - a[FirstOddIndex(a)]
{
    var firstEven: int;
    var foundEven := false;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant !foundEven ==> forall k :: 0 <= k < i ==> !IsEven(a[k])
      invariant foundEven ==> IsEven(a[firstEven])
    {
        if IsEven(a[i]) {
            firstEven := i;
            foundEven := true;
            break;
        }
    }

    var firstOdd: int;
    var foundOdd := false;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant !foundOdd ==> forall k :: 0 <= k < i ==> !IsOdd(a[k])
      invariant foundOdd ==> IsOdd(a[firstOdd])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            foundOdd := true;
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

// Auxiliary ghost functions
ghost function FirstEvenIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
{
  if IsEven(a[0]) then 0 else FirstEvenIndex(a[1..])
}

ghost function FirstOddIndex(a: array<int>): int
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
{
  if IsOdd(a[0]) then 0 else 1 + FirstOddIndex(a[1..])
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
