// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length > 0
    requires exists k :: 0 <= k < a.Length && IsEven(a[k])
    requires exists k :: 0 <= k < a.Length && IsOdd(a[k])
    ensures diff == a[FirstEvenIndex(a[..])] - a[FirstOddIndex(a[..])]
{
    var firstEven: int;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= firstEven < a.Length
        invariant (!(exists k :: 0 <= k < i && IsEven(a[k]))) ==> firstEven == 0
        invariant (exists k :: 0 <= k < i && IsEven(a[k])) ==>
                  (0 <= firstEven < i &&
                   IsEven(a[firstEven]) &&
                   (forall j :: 0 <= j < firstEven ==> !IsEven(a[j])))
    {
        if IsEven(a[i]) {
            firstEven := i;
            break;
        }
    }
    assert firstEven == FirstEvenIndex(a[..]);

    var firstOdd: int;
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= firstOdd < a.Length
        invariant (!(exists k :: 0 <= k < i && IsOdd(a[k]))) ==> firstOdd == 0
        invariant (exists k :: 0 <= k < i && IsOdd(a[k])) ==>
                  (0 <= firstOdd < i &&
                   IsOdd(a[firstOdd]) &&
                   (forall j :: 0 <= j < firstOdd ==> !IsOdd(a[j])))
    {
        if IsOdd(a[i]) {
            firstOdd := i;
            break;
        }
    }
    assert firstOdd == FirstOddIndex(a[..]);

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

function FirstEvenIndex(s: seq<int>): int
    requires |s| > 0
    requires exists k :: 0 <= k < |s| && IsEven(s[k])
    ensures 0 <= FirstEvenIndex(s) < |s|
    ensures IsEven(s[FirstEvenIndex(s)])
    ensures forall j :: 0 <= j < FirstEvenIndex(s) ==> !IsEven(s[j])
{
    FirstEvenIndexFrom(s, 0)
}

function FirstEvenIndexFrom(s: seq<int>, i: int): int
    requires 0 <= i < |s|
    requires exists k :: i <= k < |s| && IsEven(s[k])
    ensures i <= FirstEvenIndexFrom(s, i) < |s|
    ensures IsEven(s[FirstEvenIndexFrom(s, i)])
    ensures forall j :: i <= j < FirstEvenIndexFrom(s, i) ==> !IsEven(s[j])
    decreases |s| - i
{
    if IsEven(s[i]) then i else FirstEvenIndexFrom(s, i + 1)
}

function FirstOddIndex(s: seq<int>): int
    requires |s| > 0
    requires exists k :: 0 <= k < |s| && IsOdd(s[k])
    ensures 0 <= FirstOddIndex(s) < |s|
    ensures IsOdd(s[FirstOddIndex(s)])
    ensures forall j :: 0 <= j < FirstOddIndex(s) ==> !IsOdd(s[j])
{
    FirstOddIndexFrom(s, 0)
}

function FirstOddIndexFrom(s: seq<int>, i: int): int
    requires 0 <= i < |s|
    requires exists k :: i <= k < |s| && IsOdd(s[k])
    ensures i <= FirstOddIndexFrom(s, i) < |s|
    ensures IsOdd(s[FirstOddIndexFrom(s, i)])
    ensures forall j :: i <= j < FirstOddIndexFrom(s, i) ==> !IsOdd(s[j])
    decreases |s| - i
{
    if IsOdd(s[i]) then i else FirstOddIndexFrom(s, i + 1)
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
