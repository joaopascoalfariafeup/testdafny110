// Checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
  n % 2 != 0
}

ghost function FirstEvenIndexF(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures FirstEvenIndexF(lst) < |lst| && IsEven(lst[FirstEvenIndexF(lst)])
  ensures forall j :: 0 <= j < FirstEvenIndexF(lst) ==> !IsEven(lst[j])
  decreases |lst|
{
  if IsEven(lst[0]) then 0 else 1 + FirstEvenIndexF(lst[1..])
}

ghost function FirstOddIndexF(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures FirstOddIndexF(lst) < |lst| && IsOdd(lst[FirstOddIndexF(lst)])
  ensures forall j :: 0 <= j < FirstOddIndexF(lst) ==> !IsOdd(lst[j])
  decreases |lst|
{
  if IsOdd(lst[0]) then 0 else 1 + FirstOddIndexF(lst[1..])
}

// Ghost function version of "first even/odd indices", usable in specifications.
ghost function FirstEvenOddIndicesF(lst: seq<int>): (nat, nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures var e := FirstEvenOddIndicesF(lst).0; e < |lst| && IsEven(lst[e])
  ensures var e := FirstEvenOddIndicesF(lst).0; forall j :: 0 <= j < e ==> !IsEven(lst[j])
  ensures var o := FirstEvenOddIndicesF(lst).1; o < |lst| && IsOdd(lst[o])
  ensures var o := FirstEvenOddIndicesF(lst).1; forall j :: 0 <= j < o ==> !IsOdd(lst[j])
{
  (FirstEvenIndexF(lst), FirstOddIndexF(lst))
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
    invariant i < |lst| ==> (exists k :: i <= k < |lst| && IsEven(lst[k]))
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
    invariant i < |lst| ==> (exists k :: i <= k < |lst| && IsOdd(lst[k]))
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
  assert exists i :: 0 <= i < |a1| && IsEven(a1[i]);
  assert exists i :: 0 <= i < |a1| && IsOdd(a1[i]);
  var out1 := ProductFirstEvenOdd(a1);
  assert out1 == 4;

  var a2: seq<int> := [1, 5, 7, 9, 10];
  assert exists i :: 0 <= i < |a2| && IsEven(a2[i]);
  assert exists i :: 0 <= i < |a2| && IsOdd(a2[i]);
  var out2 := ProductFirstEvenOdd(a2);
  assert out2 == 10;
}
