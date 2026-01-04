// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])
  ensures exists i :: 0 <= i < |lst| && IsEven(lst[i]) && forall k :: 0 <= k < i ==> !IsEven(lst[k]) && product == lst[i] * lst[oddIndex(lst)]
  ensures exists j :: 0 <= j < |lst| && IsOdd(lst[j]) && forall k :: 0 <= k < j ==> !IsOdd(lst[k]) && product == lst[evenIndex(lst)] * lst[j]
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
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) && forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) && forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])
{
    evenIndex := 0;
    oddIndex := 0;
    var foundEven := false;
    var foundOdd := false;
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant !foundEven ==> forall k :: 0 <= k < i ==> !IsEven(lst[k])
      invariant foundEven ==> 0 <= evenIndex < i && IsEven(lst[evenIndex]) && forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])
      invariant !foundOdd ==> forall k :: 0 <= k < i ==> !IsOdd(lst[k])
      invariant foundOdd ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex]) && forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])
    {
        if !foundEven && IsEven(lst[i]) {
            evenIndex := i;
            foundEven := true;
        }
        if !foundOdd && IsOdd(lst[i]) {
            oddIndex := i;
            foundOdd := true;
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

ghost function evenIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures 0 <= evenIndex(lst) < |lst| && IsEven(lst[evenIndex(lst)]) && forall k :: 0 <= k < evenIndex(lst) ==> !IsEven(lst[k])
{
    if |lst| == 0 then 0 else
    if IsEven(lst[0]) then 0 else 1 + evenIndex(lst[1..])
}

ghost function oddIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists j :: 0 <= j < |lst| && IsOdd(lst[j])
  ensures 0 <= oddIndex(lst) < |lst| && IsOdd(lst[oddIndex(lst)]) && forall k :: 0 <= k < oddIndex(lst) ==> !IsOdd(lst[k])
{
    if |lst| == 0 then 0 else
    if IsOdd(lst[0]) then 0 else 1 + oddIndex(lst[1..])
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
