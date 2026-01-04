// Checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Ghost function version of "first even/odd indices", usable in specifications.
ghost function FirstEvenOddIndicesF(lst: seq<int>): (evenIndex: nat, oddIndex: nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures evenIndex < |lst| && IsEven(lst[evenIndex])
  ensures forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j])
  ensures oddIndex < |lst| && IsOdd(lst[oddIndex])
  ensures forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j])
{
  (FirstEvenIndexF(lst), FirstOddIndexF(lst))
}

ghost function FirstEvenIndexF(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures FirstEvenIndexF(lst) < |lst| && IsEven(lst[FirstEvenIndexF(lst)])
  ensures forall j :: 0 <= j < FirstEvenIndexF(lst) ==> !IsEven(lst[j])
{
  if IsEven(lst[0]) then 0 else 1 + FirstEvenIndexF(lst[1..])
}

ghost function FirstOddIndexF(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures FirstOddIndexF(lst) < |lst| && IsOdd(lst[FirstOddIndexF(lst)])
  ensures forall j :: 0 <= j < FirstOddIndexF(lst) ==> !IsOdd(lst[j])
{
  if IsOdd(lst[0]) then 0 else 1 + FirstOddIndexF(lst[1..])
}

// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product: int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures product == lst[FirstEvenOddIndicesF(lst).0] * lst[FirstEvenOddIndicesF(lst).1]
{
  var evenIndex, oddIndex := FirstEvenOddIndices(lst);
  product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst: seq<int>) returns (evenIndex: nat, oddIndex: nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures evenIndex < |lst| && IsEven(lst[evenIndex])
  ensures forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j])
  ensures oddIndex < |lst| && IsOdd(lst[oddIndex])
  ensures forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j])
{
  // Find first even
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> !IsEven(lst[j])
    decreases |lst| - i
  {
    if IsEven(lst[i]) {
      evenIndex := i;
      break;
    }
  }

  // Find first odd
  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> !IsOdd(lst[j])
    decreases |lst| - i
  {
    if IsOdd(lst[i]) {
      oddIndex := i;
      break;
    }
  }
}

// Test cases checked statically.
method ProductEvenOddTest() {
  var a1: seq<int> := [1, 3, 5, 7, 4, 1, 6, 8];
  var out1 := ProductFirstEvenOdd(a1);
  assert out1 == 4;

  var a2: seq<int> := [1, 5, 7, 9, 10];
  var out2 := ProductFirstEvenOdd(a2);
  assert out2 == 10;
}
