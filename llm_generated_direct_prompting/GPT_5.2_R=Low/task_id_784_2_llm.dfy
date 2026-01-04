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
  ensures FirstEvenAt(lst, evenIndex)
  ensures FirstOddAt(lst, oddIndex)
{
    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall j:nat :: j < i ==> !IsEven(lst[j])
      invariant exists k:nat :: i <= k < |lst| && IsEven(lst[k])
    {
        if IsEven(lst[i]) {
            evenIndex := i;
            break;
        }
    }
    assert FirstEvenAt(lst, evenIndex);
    FirstEvenAtImpliesIndex(lst, evenIndex);

    for i := 0 to |lst|
      invariant 0 <= i <= |lst|
      invariant forall j:nat :: j < i ==> !IsOdd(lst[j])
      invariant exists k:nat :: i <= k < |lst| && IsOdd(lst[k])
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
            break;
        }
    }
    assert FirstOddAt(lst, oddIndex);
    FirstOddAtImpliesIndex(lst, oddIndex);
}

// Checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
    n % 2 != 0
}

predicate FirstEvenAt(lst: seq<int>, idx: nat)
{
  idx < |lst| &&
  IsEven(lst[idx]) &&
  (forall j:nat :: j < idx ==> !IsEven(lst[j]))
}

predicate FirstOddAt(lst: seq<int>, idx: nat)
{
  idx < |lst| &&
  IsOdd(lst[idx]) &&
  (forall j:nat :: j < idx ==> !IsOdd(lst[j]))
}

function {:fuel 30} FirstEvenIndex(lst: seq<int>): nat
  requires exists i:nat :: i < |lst| && IsEven(lst[i])
  ensures FirstEvenAt(lst, FirstEvenIndex(lst))
{
  if IsEven(lst[0]) then 0 else 1 + FirstEvenIndex(lst[1..])
}

function {:fuel 30} FirstOddIndex(lst: seq<int>): nat
  requires exists i:nat :: i < |lst| && IsOdd(lst[i])
  ensures FirstOddAt(lst, FirstOddIndex(lst))
{
  if IsOdd(lst[0]) then 0 else 1 + FirstOddIndex(lst[1..])
}

lemma {:fuel 30} FirstEvenAtImpliesIndex(lst: seq<int>, idx: nat)
  requires exists i:nat :: i < |lst| && IsEven(lst[i])
  requires FirstEvenAt(lst, idx)
  ensures idx == FirstEvenIndex(lst)
  decreases idx
{
  if idx == 0 {
  } else {
    assert !IsEven(lst[0]);
    assert idx - 1 < |lst[1..]|;
    assert lst[1..][idx - 1] == lst[idx];
    assert IsEven(lst[1..][idx - 1]);
    assert forall j:nat :: j < idx - 1 ==> !IsEven(lst[1..][j]);
    assert FirstEvenAt(lst[1..], idx - 1);

    assert exists i:nat :: i < |lst[1..]| && IsEven(lst[1..][i]) by {
      var w :| 0 <= w < |lst| && IsEven(lst[w]);
      assert w != 0;
      assert w - 1 < |lst[1..]|;
      assert lst[1..][w - 1] == lst[w];
    }

    FirstEvenAtImpliesIndex(lst[1..], idx - 1);
  }
}

lemma {:fuel 30} FirstOddAtImpliesIndex(lst: seq<int>, idx: nat)
  requires exists i:nat :: i < |lst| && IsOdd(lst[i])
  requires FirstOddAt(lst, idx)
  ensures idx == FirstOddIndex(lst)
  decreases idx
{
  if idx == 0 {
  } else {
    assert !IsOdd(lst[0]);
    assert idx - 1 < |lst[1..]|;
    assert lst[1..][idx - 1] == lst[idx];
    assert IsOdd(lst[1..][idx - 1]);
    assert forall j:nat :: j < idx - 1 ==> !IsOdd(lst[1..][j]);
    assert FirstOddAt(lst[1..], idx - 1);

    assert exists i:nat :: i < |lst[1..]| && IsOdd(lst[1..][i]) by {
      var w :| 0 <= w < |lst| && IsOdd(lst[w]);
      assert w != 0;
      assert w - 1 < |lst[1..]|;
      assert lst[1..][w - 1] == lst[w];
    }

    FirstOddAtImpliesIndex(lst[1..], idx - 1);
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
