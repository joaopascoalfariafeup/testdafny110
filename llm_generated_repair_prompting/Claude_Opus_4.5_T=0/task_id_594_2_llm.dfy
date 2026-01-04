// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i :: 0 <= i < a.Length && IsEven(a[i]) && (forall j :: 0 <= j < i ==> !IsEven(a[j])) && exists k :: 0 <= k < a.Length && IsOdd(a[k]) && (forall m :: 0 <= m < k ==> !IsOdd(a[m])) && diff == a[i] - a[k]
{
    var firstEven: int := -1;
    for i := 0 to a.Length
        invariant firstEven == -1 ==> forall j :: 0 <= j < i ==> !IsEven(a[j])
        invariant firstEven != -1 ==> 0 <= firstEven < i && IsEven(a[firstEven]) && forall j :: 0 <= j < firstEven ==> !IsEven(a[j])
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }

    var firstOdd: int := -1;
    for i := 0 to a.Length
        invariant firstOdd == -1 ==> forall j :: 0 <= j < i ==> !IsOdd(a[j])
        invariant firstOdd != -1 ==> 0 <= firstOdd < i && IsOdd(a[firstOdd]) && forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j])
        invariant 0 <= firstEven < a.Length && IsEven(a[firstEven]) && forall j :: 0 <= j < firstEven ==> !IsEven(a[j])
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

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest(){
    var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
    assert a1[..] == [1, 3, 5, 7, 4, 1, 6, 8];
    assert IsEven(a1[4]);  // 4 is even
    assert IsOdd(a1[0]);   // 1 is odd
    var out1 := FirstEvenOddDifference(a1);
    assert a1[4] == 4 && a1[0] == 1;
    assert !IsEven(a1[0]) && !IsEven(a1[1]) && !IsEven(a1[2]) && !IsEven(a1[3]);
    assert out1 == 3;

    var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    assert a2[..] == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    assert IsEven(a2[1]);  // 2 is even
    assert IsOdd(a2[0]);   // 1 is odd
    var out2 := FirstEvenOddDifference(a2);
    assert a2[1] == 2 && a2[0] == 1;
    assert !IsEven(a2[0]);
    assert out2 == 1;

    var a3:= new int[] [1, 5, 7, 9, 10];
    assert a3[..] == [1, 5, 7, 9, 10];
    assert IsEven(a3[4]);  // 10 is even
    assert IsOdd(a3[0]);   // 1 is odd
    var out3 := FirstEvenOddDifference(a3);
    assert a3[4] == 10 && a3[0] == 1;
    assert !IsEven(a3[0]) && !IsEven(a3[1]) && !IsEven(a3[2]) && !IsEven(a3[3]);
    assert out3 == 9;
}
