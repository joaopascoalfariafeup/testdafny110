// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i:nat :: i < |lst| && IsEven(lst[i])
  requires exists i:nat :: i < |lst| && IsOdd(lst[i])
  ensures product == lst[FirstEvenIndex(lst)] * lst[FirstOddIndex(lst)]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i:nat :: i < |lst| && IsEven(lst[i])
  requires exists i:nat :: i < |lst| && IsOdd(lst[i])
  ensures evenIndex == FirstEvenIndex(lst)
  ensures oddIndex == FirstOddIndex(lst)
{
    ghost var foundEven := false;
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant !foundEven ==> (forall j:nat :: 0 <= j < i ==> !IsEven(lst[j]))
      invariant foundEven ==> evenIndex < |lst| && IsEven(lst[evenIndex]) && (forall j:nat :: 0 <= j < evenIndex ==> !IsEven(lst[j]))
    {
        if IsEven(lst[i]) {
            ghost foundEven := true;
            evenIndex := i;
            break;
        }
    }
    if !foundEven {
        assert forall j:nat :: 0 <= j < |lst| ==> !IsEven(lst[j]);
        assert false;
    }

    ghost var foundOdd := false;
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant !foundOdd ==> (forall j:nat :: 0 <= j < i ==> !IsOdd(lst[j]))
      invariant foundOdd ==> oddIndex < |lst| && IsOdd(lst[oddIndex]) && (forall j:nat :: 0 <= j < oddIndex ==> !IsOdd(lst[j]))
    {
        if IsOdd(lst[i]) {
            ghost foundOdd := true;
            oddIndex := i;
            break;
        }
    }
    if !foundOdd {
        assert forall j:nat :: 0 <= j < |lst| ==> !IsOdd(lst[j]);
        assert false;
    }

    assert evenIndex < |lst| && IsEven(lst[evenIndex]) && (forall j:nat :: 0 <= j < evenIndex ==> !IsEven(lst[j]));
    assert oddIndex < |lst| && IsOdd(lst[oddIndex]) && (forall j:nat :: 0 <= j < oddIndex ==> !IsOdd(lst[j]));
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
  requires exists i:nat :: i < |lst| && IsEven(lst[i])
  ensures FirstEvenIndex(lst) < |lst|
  ensures IsEven(lst[FirstEvenIndex(lst)])
  ensures forall j:nat :: 0 <= j < FirstEvenIndex(lst) ==> !IsEven(lst[j])
{
  var i :| i < |lst| && IsEven(lst[i]) && (forall j:nat :: 0 <= j < i ==> !IsEven(lst[j]));
  i
}

function FirstOddIndex(lst: seq<int>): nat
  requires exists i:nat :: i < |lst| && IsOdd(lst[i])
  ensures FirstOddIndex(lst) < |lst|
  ensures IsOdd(lst[FirstOddIndex(lst)])
  ensures forall j:nat :: 0 <= j < FirstOddIndex(lst) ==> !IsOdd(lst[j])
{
  var i :| i < |lst| && IsOdd(lst[i]) && (forall j:nat :: 0 <= j < i ==> !IsOdd(lst[j]));
  i
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
