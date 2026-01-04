// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures exists ie, io :: FirstEvenIndex(a[..], ie) && FirstOddIndex(a[..], io) && diff == a[ie] - a[io]
{
    var firstEven: int;
    for i := 0 to a.Length
      invariant forall j :: 0 <= j < i ==> !IsEven(a[j])
    {
        if IsEven(a[i]) {
            firstEven := i;
            assert 0 <= firstEven < a.Length;
            assert IsEven(a[firstEven]);
            assert forall j :: 0 <= j < firstEven ==> !IsEven(a[j]);
            break;
        }
    }
    assert 0 <= firstEven < a.Length;
    assert IsEven(a[firstEven]);
    assert forall j :: 0 <= j < firstEven ==> !IsEven(a[j]);

    var firstOdd: int;
    for i := 0 to a.Length
      invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            assert 0 <= firstOdd < a.Length;
            assert IsOdd(a[firstOdd]);
            assert forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]);
            break;
        }
    }
    assert 0 <= firstOdd < a.Length;
    assert IsOdd(a[firstOdd]);
    assert forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j]);

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

predicate FirstEvenIndex(s: seq<int>, i: int)
{
  0 <= i < |s| &&
  IsEven(s[i]) &&
  forall j :: 0 <= j < i ==> !IsEven(s[j])
}

predicate FirstOddIndex(s: seq<int>, i: int)
{
  0 <= i < |s| &&
  IsOdd(s[i]) &&
  forall j :: 0 <= j < i ==> !IsOdd(s[j])
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
