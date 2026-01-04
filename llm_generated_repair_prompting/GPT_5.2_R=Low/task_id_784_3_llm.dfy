// Checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Checks if a number is odd.
predicate IsOdd(n: int) {
  n % 2 != 0
}

lemma EvenExistsInTail(lst: seq<int>)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires !IsEven(lst[0])
  ensures exists i :: 0 <= i < |lst[1..]| && IsEven(lst[1..][i])
{
  var k :| 0 <= k < |lst| && IsEven(lst[k]);
  assert k != 0;
  assert 1 <= k < |lst|;
  assert 0 <= k-1 < |lst|-1;
  assert lst[1..][k-1] == lst[k];
}

lemma OddExistsInTail(lst: seq<int>)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  requires !IsOdd(lst[0])
  ensures exists i :: 0 <= i < |lst[1..]| && IsOdd(lst[1..][i])
{
  var k :| 0 <= k < |lst| && IsOdd(lst[k]);
  assert k != 0;
  assert 1 <= k < |lst|;
  assert 0 <= k-1 < |lst|-1;
  assert lst[1..][k-1] == lst[k];
}

ghost function {:fuel 20} firstEvenIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  ensures firstEvenIndex(lst) < |lst|
  ensures IsEven(lst[firstEvenIndex(lst)])
  ensures forall j :: 0 <= j < firstEvenIndex(lst) ==> !IsEven(lst[j])
{
  if IsEven(lst[0]) then 0
  else
    1 + firstEvenIndex(lst[1..])
}

ghost function {:fuel 20} firstOddIndex(lst: seq<int>): nat
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures firstOddIndex(lst) < |lst|
  ensures IsOdd(lst[firstOddIndex(lst)])
  ensures forall j :: 0 <= j < firstOddIndex(lst) ==> !IsOdd(lst[j])
{
  if IsOdd(lst[0]) then 0
  else
    1 + firstOddIndex(lst[1..])
}

lemma FirstEvenIndexCharacterization(lst: seq<int>, i: nat)
  requires |lst| > 0
  requires exists k :: 0 <= k < |lst| && IsEven(lst[k])
  requires i < |lst|
  requires IsEven(lst[i])
  requires forall j :: 0 <= j < i ==> !IsEven(lst[j])
  ensures firstEvenIndex(lst) == i
{
  var fe := firstEvenIndex(lst);
  assert fe < |lst| && IsEven(lst[fe]);
  assert forall j :: 0 <= j < fe ==> !IsEven(lst[j]);

  if i < fe {
    assert 0 <= i < fe;
    assert !IsEven(lst[i]);
    assert false;
  }

  if fe < i {
    assert 0 <= fe < i;
    assert !IsEven(lst[fe]);
    assert false;
  }
}

lemma FirstOddIndexCharacterization(lst: seq<int>, i: nat)
  requires |lst| > 0
  requires exists k :: 0 <= k < |lst| && IsOdd(lst[k])
  requires i < |lst|
  requires IsOdd(lst[i])
  requires forall j :: 0 <= j < i ==> !IsOdd(lst[j])
  ensures firstOddIndex(lst) == i
{
  var fo := firstOddIndex(lst);
  assert fo < |lst| && IsOdd(lst[fo]);
  assert forall j :: 0 <= j < fo ==> !IsOdd(lst[j]);

  if i < fo {
    assert 0 <= i < fo;
    assert !IsOdd(lst[i]);
    assert false;
  }

  if fo < i {
    assert 0 <= fo < i;
    assert !IsOdd(lst[fo]);
    assert false;
  }
}

// Returns the product of the first even and first odd elements in the list.
// The list must contain at least one even and one odd element.
method ProductFirstEvenOdd(lst: seq<int>) returns (product : int)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures product == lst[firstEvenIndex(lst)] * lst[firstOddIndex(lst)]
{
  var evenIndex, oddIndex := FirstEvenOddIndices(lst);
  product := lst[evenIndex] * lst[oddIndex];
}

// Obtains the indices of the first even and odd elements in the list.
// The list must contain at least one even and one odd element.
method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: nat, oddIndex : nat)
  requires |lst| > 0
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures evenIndex == firstEvenIndex(lst)
  ensures oddIndex == firstOddIndex(lst)
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
    invariant i < |lst| ==> (exists k :: i <= k < |lst| && IsEven(lst[k]))
  {
    if IsEven(lst[i]) {
      evenIndex := i;
      break;
    } else {
      if i + 1 < |lst| {
        assert exists k :: i <= k < |lst| && IsEven(lst[k]);
        var k :| i <= k < |lst| && IsEven(lst[k]);
        assert k != i;
        assert i + 1 <= k < |lst|;
        assert exists k2 :: i + 1 <= k2 < |lst| && IsEven(lst[k2]);
      }
    }
  }
  assert IsEven(lst[evenIndex]);
  assert forall j :: 0 <= j < evenIndex ==> !IsEven(lst[j]);
  assert evenIndex < |lst|;
  FirstEvenIndexCharacterization(lst, evenIndex);

  for i := 0 to |lst|
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> !IsOdd(lst[j])
    invariant i < |lst| ==> (exists k :: i <= k < |lst| && IsOdd(lst[k]))
  {
    if IsOdd(lst[i]) {
      oddIndex := i;
      break;
    } else {
      if i + 1 < |lst| {
        assert exists k :: i <= k < |lst| && IsOdd(lst[k]);
        var k :| i <= k < |lst| && IsOdd(lst[k]);
        assert k != i;
        assert i + 1 <= k < |lst|;
        assert exists k2 :: i + 1 <= k2 < |lst| && IsOdd(lst[k2]);
      }
    }
  }
  assert IsOdd(lst[oddIndex]);
  assert forall j :: 0 <= j < oddIndex ==> !IsOdd(lst[j]);
  assert oddIndex < |lst|;
  FirstOddIndexCharacterization(lst, oddIndex);
}

// Test cases checked statically.
method ProductEvenOddTest(){
  var a1: seq<int> := [1, 3, 5, 7, 4, 1, 6, 8];
  // Help the verifier establish the required existentials
  assert IsOdd(a1[0]);
  assert IsEven(a1[4]);
  assert exists i :: 0 <= i < |a1| && IsOdd(a1[i]);
  assert exists i :: 0 <= i < |a1| && IsEven(a1[i]);

  var out1 := ProductFirstEvenOdd(a1);

  // Prove: all positions < 4 are not even
  forall j | 0 <= j < 4
    ensures !IsEven(a1[j])
  {
    if j == 0 { assert !IsEven(a1[0]); }
    else if j == 1 { assert !IsEven(a1[1]); }
    else if j == 2 { assert !IsEven(a1[2]); }
    else { assert j == 3; assert !IsEven(a1[3]); }
  }
  assert forall j :: 0 <= j < 4 ==> !IsEven(a1[j]);

  assert forall j :: 0 <= j < 0 ==> !IsOdd(a1[j]);

  assert firstEvenIndex(a1) == 4 by {
    FirstEvenIndexCharacterization(a1, 4);
  }
  assert firstOddIndex(a1) == 0 by {
    FirstOddIndexCharacterization(a1, 0);
  }
  assert out1 == 4;

  var a2: seq<int> := [1, 5, 7, 9, 10];
  assert IsOdd(a2[0]);
  assert IsEven(a2[4]);
  assert exists i :: 0 <= i < |a2| && IsOdd(a2[i]);
  assert exists i :: 0 <= i < |a2| && IsEven(a2[i]);

  var out2 := ProductFirstEvenOdd(a2);

  forall j | 0 <= j < 4
    ensures !IsEven(a2[j])
  {
    if j == 0 { assert !IsEven(a2[0]); }
    else if j == 1 { assert !IsEven(a2[1]); }
    else if j == 2 { assert !IsEven(a2[2]); }
    else { assert j == 3; assert !IsEven(a2[3]); }
  }
  assert forall j :: 0 <= j < 4 ==> !IsEven(a2[j]);

  assert forall j :: 0 <= j < 0 ==> !IsOdd(a2[j]);

  assert firstEvenIndex(a2) == 4 by {
    FirstEvenIndexCharacterization(a2, 4);
  }
  assert firstOddIndex(a2) == 0 by {
    FirstOddIndexCharacterization(a2, 0);
  }
  assert out2 == 10;
}
