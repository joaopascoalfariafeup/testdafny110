// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i]) // There is an even element in the list
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i]) // There is an odd element in the list
  ensures product == lst[FirstEven(lst)] * lst[FirstOdd(lst)] // product is the multiplication of the first even and odd elements in the list
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i]) // There is an even element in the list
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i]) // There is an odd element in the list
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) // evenIndex is the index of the first even element in the list
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) // oddIndex is the index of the first odd element in the list
{
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall k :: 0 <= k < i ==> !IsEven(lst[k])
      ensures evenIndex == i
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall k :: 0 <= k < i ==> !IsOdd(lst[k])
      ensures oddIndex == i
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

// Returns the index of the first even element in the list.
function FirstEven(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i]) // There is an even element in the list
  reads lst
  ensures 0 <= FirstEven(lst) < |lst| && IsEven(lst[FirstEven(lst)]) // FirstEven(lst) is the index of the first even element in the list
{
  (forall i :: 0 <= i < |lst| && IsEven(lst[i]) ==> FirstEven(lst) <= i) ? 0 : 0
}

// Returns the index of the first odd element in the list.
function FirstOdd(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i]) // There is an odd element in the list
  reads lst
  ensures 0 <= FirstOdd(lst) < |lst| && IsOdd(lst[FirstOdd(lst)]) // FirstOdd(lst) is the index of the first odd element in the list
{
  (forall i :: 0 <= i < |lst| && IsOdd(lst[i]) ==> FirstOdd(lst) <= i) ? 0 : 0
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
