// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])
  ensures product == lst[FirstEvenIndex(lst)] * lst[FirstOddIndex(lst)]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex])
  ensures forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex])
  ensures forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])
{
    evenIndex := 0;
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant evenIndex == 0 && i == 0 || (0 <= evenIndex < i && IsEven(lst[evenIndex]))
      invariant forall k :: 0 <= k < i ==> !IsEven(lst[k]) || k >= evenIndex
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }

    oddIndex := 0;
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant oddIndex == 0 && i == 0 || (0 <= oddIndex < i && IsOdd(lst[oddIndex]))
      invariant forall k :: 0 <= k < i ==> !IsOdd(lst[k]) || k >= oddIndex
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

ghost function FirstEvenIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures 0 <= FirstEvenIndex(lst) < |lst|
  ensures IsEven(lst[FirstEvenIndex(lst)])
  ensures forall k :: 0 <= k < FirstEvenIndex(lst) ==> !IsEven(lst[k])
{
  if |lst| == 0 then 0
  else if IsEven(lst[0]) then 0
  else 1 + FirstEvenIndex(lst[1..])
}

ghost function FirstOddIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])
  ensures 0 <= FirstOddIndex(lst) < |lst|
  ensures IsOdd(lst[FirstOddIndex(lst)])
  ensures forall k :: 0 <= k < FirstOddIndex(lst) ==> !IsOdd(lst[k])
{
  if |lst| == 0 then 0
  else if IsOdd(lst[0]) then 0
  else 1 + FirstOddIndex(lst[1..])
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
