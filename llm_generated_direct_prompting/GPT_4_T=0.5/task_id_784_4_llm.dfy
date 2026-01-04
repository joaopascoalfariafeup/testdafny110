// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])  // list contains at least one even number
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])   // list contains at least one odd number
  ensures product == lst[FirstEven(lst)] * lst[FirstOdd(lst)]  // product is the multiplication of first even and odd numbers
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])  // list contains at least one even number
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])   // list contains at least one odd number
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) && forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])  // evenIndex is the first even index
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) && forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])  // oddIndex is the first odd index
{
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant i == 0 || !IsEven(lst[i-1])
      decreases |lst| - i
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant i == 0 || !IsOdd(lst[i-1])
      decreases |lst| - i
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

ghost function FirstEven(lst: seq<int>) returns (i: nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures 0 <= i < |lst| && IsEven(lst[i]) && forall k :: 0 <= k < i ==> !IsEven(lst[k])
{
  if IsEven(lst[0]) then 0
  else 1 + FirstEven(lst[1..])
}

ghost function FirstOdd(lst: seq<int>) returns (i: nat)
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= i < |lst| && IsOdd(lst[i]) && forall k :: 0 <= k < i ==> !IsOdd(lst[k])
{
  if IsOdd(lst[0]) then 0
  else 1 + FirstOdd(lst[1..])
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
