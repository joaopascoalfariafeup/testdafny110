// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: (0 <= i < |lst| && 0 <= j < |lst| && IsEven(lst[i]) && IsOdd(lst[j]) && 
            (forall k :: 0 <= k < i ==> !IsEven(lst[k])) && 
            (forall k :: 0 <= k < j ==> !IsOdd(lst[k])) && 
            product == lst[i] * lst[j])
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures evenIndex < |lst| && IsEven(lst[evenIndex])
    ensures forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])
    ensures oddIndex < |lst| && IsOdd(lst[oddIndex])
    ensures forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])
{
    for i := 0 to |lst|
        invariant forall k :: 0 <= k < i ==> !IsEven(lst[k])
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }

    for i := 0 to |lst|
        invariant forall k :: 0 <= k < i ==> !IsOdd(lst[k])
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
            break;
        }
    }
}

// Checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
    n % 2 != 0
}




// Test cases checked statically.
method ProductEvenOddTest(){
    var a1: seq<int> := [1, 3, 5, 7, 4, 1, 6, 8];
    // Help Dafny see that preconditions are satisfied
    assert IsOdd(a1[0]);  // 1 is odd
    assert IsEven(a1[4]); // 4 is even
    assert exists i :: 0 <= i < |a1| && IsOdd(a1[i]);
    assert exists i :: 0 <= i < |a1| && IsEven(a1[i]);
    // First odd is at index 0 (value 1), first even is at index 4 (value 4)
    assert forall k :: 0 <= k < 0 ==> !IsOdd(a1[k]);
    assert forall k :: 0 <= k < 4 ==> !IsEven(a1[k]);
    var out1 := ProductFirstEvenOdd(a1);
    assert a1[0] == 1 && a1[4] == 4;
    assert 1 * 4 == 4;
    assert out1 == 4;


    var a2: seq<int> := [1, 5, 7, 9, 10];
    // Help Dafny see that preconditions are satisfied
    assert IsOdd(a2[0]);  // 1 is odd
    assert IsEven(a2[4]); // 10 is even
    assert exists i :: 0 <= i < |a2| && IsOdd(a2[i]);
    assert exists i :: 0 <= i < |a2| && IsEven(a2[i]);
    // First odd is at index 0 (value 1), first even is at index 4 (value 10)
    assert forall k :: 0 <= k < 0 ==> !IsOdd(a2[k]);
    assert forall k :: 0 <= k < 4 ==> !IsEven(a2[k]);
    var out2 := ProductFirstEvenOdd(a2);
    assert a2[0] == 1 && a2[4] == 10;
    assert 1 * 10 == 10;
    assert out2 == 10;
}
