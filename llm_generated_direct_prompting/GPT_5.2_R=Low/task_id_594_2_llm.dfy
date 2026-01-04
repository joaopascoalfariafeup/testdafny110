// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires ExistsEven(a)
  requires ExistsOdd(a)
  ensures exists e, o :: IsFirstEvenIndex(a, e) && IsFirstOddIndex(a, o) && diff == a[e] - a[o]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> !IsEven(a[k])
    {
        if IsEven(a[i]) {
            firstEven := i;
            assert IsFirstEvenIndex(a, firstEven);
            break;
        }
    }
    assert IsFirstEvenIndex(a, firstEven);

    var firstOdd: int;
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            assert IsFirstOddIndex(a, firstOdd);
            break;
        }
    }
    assert IsFirstOddIndex(a, firstOdd);

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

predicate ExistsEven(a: array<int>)
  reads a
{
  exists i :: 0 <= i < a.Length && IsEven(a[i])
}

predicate ExistsOdd(a: array<int>)
  reads a
{
  exists i :: 0 <= i < a.Length && IsOdd(a[i])
}

predicate IsFirstEvenIndex(a: array<int>, idx: int)
  reads a
{
  0 <= idx < a.Length &&
  IsEven(a[idx]) &&
  forall k :: 0 <= k < idx ==> !IsEven(a[k])
}

predicate IsFirstOddIndex(a: array<int>, idx: int)
  reads a
{
  0 <= idx < a.Length &&
  IsOdd(a[idx]) &&
  forall k :: 0 <= k < idx ==> !IsOdd(a[k])
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
