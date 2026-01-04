// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i]) // At least one even number is required in the list.
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i]) // At least one odd number is required in the list.
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i]) // At least one even number is required in the list.
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i]) // At least one odd number is required in the list.
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) // The returned evenIndex is valid and points to an even number.
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) // The returned oddIndex is valid and points to an odd number.
{
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant i == 0 || (0 <= evenIndex < i && IsEven(lst[evenIndex]))
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant i == 0 || (0 <= oddIndex < i && IsOdd(lst[oddIndex]))
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
    var out1 := ProductFirstEvenOdd(a1);
    assert out1 == 4;

    var a2: seq<int> := [1, 5, 7, 9, 10];
    var out2 := ProductFirstEvenOdd(a2);
    assert out2 == 10;
}
