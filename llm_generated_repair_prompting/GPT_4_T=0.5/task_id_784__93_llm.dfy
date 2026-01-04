// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) && 
          (forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k]))
  ensures 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) && 
          (forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k]))
{
    var foundEven, foundOdd := false, false; // Initialize foundEven and foundOdd to track if even and odd numbers are found.
    evenIndex, oddIndex := 0, 0;

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant foundEven ==> (0 <= evenIndex < i && IsEven(lst[evenIndex]) && 
                               (forall k :: 0 <= k < evenIndex ==> !IsEven(lst[k])))
      invariant !foundEven ==> (forall k :: 0 <= k < i ==> !IsEven(lst[k]))
    {
        if !foundEven && IsEven(lst[i]) {
            evenIndex := i;
            foundEven := true;
        }
    }

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant foundOdd ==> (0 <= oddIndex < i && IsOdd(lst[oddIndex]) && 
                              (forall k :: 0 <= k < oddIndex ==> !IsOdd(lst[k])))
      invariant !foundOdd ==> (forall k :: 0 <= k < i ==> !IsOdd(lst[k]))
    {
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

// Test cases checked statically.
method ProductEvenOddTest(){
    var a1: seq<int> := [1, 3, 5, 7, 4, 1, 6, 8];
    assert a1[..] == [1, 3, 5, 7, 4, 1, 6, 8]; // helper
    assert exists i :: 0 <= i < |a1| && IsEven(a1[i]);
    assert exists i :: 0 <= i < |a1| && IsOdd(a1[i]);
    var out1 := ProductFirstEvenOdd(a1);
    assert out1 == 4;

    var a2: seq<int> := [1, 5, 7, 9, 10];
    assert a2[..] == [1, 5, 7, 9, 10]; // helper
    assert exists i :: 0 <= i < |a2| && IsEven(a2[i]);
    assert exists i :: 0 <= i < |a2| && IsOdd(a2[i]);
    var out2 := ProductFirstEvenOdd(a2);
    assert out2 == 10;
}
