// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures exists ei, oi :: 0 <= ei < |lst| && 0 <= oi < |lst| &&
                          IsEven(lst[ei]) && (forall j :: 0 <= j < ei ==> !IsEven(lst[j])) &&
                          IsOdd(lst[oi])  && (forall j :: 0 <= j < oi ==> !IsOdd(lst[j])) &&
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
  ensures evenIndex < |lst|
  ensures IsEven(lst[evenIndex])
  ensures forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j])
  ensures oddIndex < |lst|
  ensures IsOdd(lst[oddIndex])
  ensures forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j])
{
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall j :: 0 <= j < i ==> !IsEven(lst[j])
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }
    assert IsEven(lst[evenIndex]);
    assert forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j]);

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall j :: 0 <= j < i ==> !IsOdd(lst[j])
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
            break;
        }
    }
    assert IsOdd(lst[oddIndex]);
    assert forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j]);
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
