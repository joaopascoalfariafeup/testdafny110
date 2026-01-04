// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures exists ei, oi :: 0 <= ei < |lst| && 0 <= oi < |lst| &&
            IsEven(lst[ei]) && (forall k :: 0 <= k < ei ==> !IsEven(lst[k])) &&
            IsOdd(lst[oi]) && (forall k :: 0 <= k < oi ==> !IsOdd(lst[k])) &&
            product == lst[ei] * lst[oi]
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
    assert evenIndex < |lst| && IsEven(lst[evenIndex]);

    for i := 0 to |lst|
      invariant forall k :: 0 <= k < i ==> !IsOdd(lst[k])
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
            break;
        }
    }
    assert oddIndex < |lst| && IsOdd(lst[oddIndex]);
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
    var out1 := ProductFirstEvenOdd(a1);
    assert out1 == 4;


    var a2: seq<int> := [1, 5, 7, 9, 10];
    var out2 := ProductFirstEvenOdd(a2);
    assert out2 == 10;
}
