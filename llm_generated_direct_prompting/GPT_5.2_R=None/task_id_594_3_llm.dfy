// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures diff == a[FindFirstEvenIndex(a)] - a[FindFirstOddIndex(a)]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant exists j :: 0 <= j < a.Length && IsEven(a[j])
      invariant (forall j :: 0 <= j < i ==> !IsEven(a[j]))
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }

    var firstOdd: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant exists j :: 0 <= j < a.Length && IsOdd(a[j])
      invariant (forall j :: 0 <= j < i ==> !IsOdd(a[j]))
    {
        if IsOdd(a[i]) {
            firstOdd := i;
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

ghost function FindFirstEvenIndex(a: array<int>): int
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  ensures 0 <= FindFirstEvenIndex(a) < a.Length
  ensures IsEven(a[FindFirstEvenIndex(a)])
  ensures forall j :: 0 <= j < FindFirstEvenIndex(a) ==> !IsEven(a[j])
{
  choose i | 0 <= i < a.Length && IsEven(a[i]) && (forall j :: 0 <= j < i ==> !IsEven(a[j]))
}

ghost function FindFirstOddIndex(a: array<int>): int
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures 0 <= FindFirstOddIndex(a) < a.Length
  ensures IsOdd(a[FindFirstOddIndex(a)])
  ensures forall j :: 0 <= j < FindFirstOddIndex(a) ==> !IsOdd(a[j])
{
  choose i | 0 <= i < a.Length && IsOdd(a[i]) && (forall j :: 0 <= j < i ==> !IsOdd(a[j]))
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
