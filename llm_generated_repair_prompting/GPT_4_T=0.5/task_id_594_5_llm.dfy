// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])  // At least one even number
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])   // At least one odd number
  ensures 
    (exists i :: 0 <= i < a.Length && IsEven(a[i]) && 
      exists j :: 0 <= j < a.Length && IsOdd(a[j]) && 
      i <= j) ==> diff == a[FirstIndexOf(a, IsEven)] - a[FirstIndexOf(a, IsOdd)]
    ||
    (exists i :: 0 <= i < a.Length && IsEven(a[i]) && 
      exists j :: 0 <= j < a.Length && IsOdd(a[j]) && 
      i > j) ==> diff == 0
{
    var firstEven: int := -1;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant firstEven == -1 || (0 <= firstEven < i && IsEven(a[firstEven]))
      invariant forall j :: 0 <= j < i && IsEven(a[j]) ==> firstEven != -1
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }

    var firstOdd: int := -1;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant firstOdd == -1 || (0 <= firstOdd < i && IsOdd(a[firstOdd]))
      invariant forall j :: 0 <= j < i && IsOdd(a[j]) ==> firstOdd != -1
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            break;
        }
    }

    diff := a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

// Auxiliary function
function FirstIndexOf(a: array<int>, pred: int -> bool): int
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && pred(a[i])
  ensures 0 <= FirstIndexOf(a, pred) < a.Length && pred(a[FirstIndexOf(a, pred)])
  ensures forall i :: 0 <= i < FirstIndexOf(a, pred) ==> !pred(a[i])
{
  var i := 0;
  while !pred(a[i])
    invariant 0 <= i < a.Length
  {
    i := i + 1;
  }
  i
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest(){
    var a1 := new int[8]; a1[0], a1[1], a1[2], a1[3], a1[4], a1[5], a1[6], a1[7] := 1, 3, 5, 7, 4, 1, 6, 8;
    assert exists i :: 0 <= i < a1.Length && IsEven(a1[i]); // Helper assertion
    assert exists i :: 0 <= i < a1.Length && IsOdd(a1[i]);  // Helper assertion
    var out1 := FirstEvenOddDifference(a1);
    assert out1 == 3;

    var a2 := new int[10]; a2[0], a2[1], a2[2], a2[3], a2[4], a2[5], a2[6], a2[7], a2[8], a2[9] := 1, 2, 3, 4, 5, 6, 7, 8, 9, 10;
    assert exists i :: 0 <= i < a2.Length && IsEven(a2[i]); // Helper assertion
    assert exists i :: 0 <= i < a2.Length && IsOdd(a2[i]);  // Helper assertion
    var out2 := FirstEvenOddDifference(a2);
    assert out2 == 1;

    var a3 := new int[5]; a3[0], a3[1], a3[2], a3[3], a3[4] := 1, 5, 7, 9, 10;
    assert exists i :: 0 <= i < a3.Length && IsEven(a3[i]); // Helper assertion
    assert exists i :: 0 <= i < a3.Length && IsOdd(a3[i]);  // Helper assertion
    var out3 := FirstEvenOddDifference(a3);
    assert out3 == 9;
}
