// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures product == lst[FirstEvenIndex(lst)] * lst[FirstOddIndex(lst)]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures evenIndex == FirstEvenIndex(lst)
  ensures oddIndex == FirstOddIndex(lst)
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

    assert 0 <= evenIndex < |lst|;
    assert IsEven(lst[evenIndex]);
    assert forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j]);
    FirstEvenIndexUnique(lst, evenIndex);

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall j :: 0 <= j < i ==> !IsOdd(lst[j])
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
            break;
        }
    }

    assert 0 <= oddIndex < |lst|;
    assert IsOdd(lst[oddIndex]);
    assert forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j]);
    FirstOddIndexUnique(lst, oddIndex);
}

// Checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
    n % 2 != 0
}

function FirstEvenIndex(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures 0 <= FirstEvenIndex(lst) < |lst|
  ensures IsEven(lst[FirstEvenIndex(lst)])
  ensures forall j :: 0 <= j < FirstEvenIndex(lst) ==> !IsEven(lst[j])
{
  var i :| 0 <= i < |lst| && IsEven(lst[i]) && (forall j :: 0 <= j < i ==> !IsEven(lst[j]));
  i
}

function FirstOddIndex(lst: seq<int>): nat
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= FirstOddIndex(lst) < |lst|
  ensures IsOdd(lst[FirstOddIndex(lst)])
  ensures forall j :: 0 <= j < FirstOddIndex(lst) ==> !IsOdd(lst[j])
{
  var i :| 0 <= i < |lst| && IsOdd(lst[i]) && (forall j :: 0 <= j < i ==> !IsOdd(lst[j]));
  i
}

lemma FirstEvenIndexUnique(lst: seq<int>, i: nat)
  requires exists k :: 0 <= k < |lst| && IsEven(lst[k])
  requires 0 <= i < |lst|
  requires IsEven(lst[i])
  requires forall j :: 0 <= j < i ==> !IsEven(lst[j])
  ensures i == FirstEvenIndex(lst)
{
  var fi := FirstEvenIndex(lst);

  if fi < i {
    assert 0 <= fi < i;
    assert !IsEven(lst[fi]);
    assert IsEven(lst[fi]);
  }
  if i < fi {
    assert 0 <= i < fi;
    assert !IsEven(lst[i]);
    assert IsEven(lst[i]);
  }
}

lemma FirstOddIndexUnique(lst: seq<int>, i: nat)
  requires exists k :: 0 <= k < |lst| && IsOdd(lst[k])
  requires 0 <= i < |lst|
  requires IsOdd(lst[i])
  requires forall j :: 0 <= j < i ==> !IsOdd(lst[j])
  ensures i == FirstOddIndex(lst)
{
  var fi := FirstOddIndex(lst);

  if fi < i {
    assert 0 <= fi < i;
    assert !IsOdd(lst[fi]);
    assert IsOdd(lst[fi]);
  }
  if i < fi {
    assert 0 <= i < fi;
    assert !IsOdd(lst[i]);
    assert IsOdd(lst[i]);
  }
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
