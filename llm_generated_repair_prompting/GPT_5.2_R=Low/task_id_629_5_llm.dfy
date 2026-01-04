// Predicate that checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

function {:fuel 10} FilterEvens(s: seq<int>): seq<int>
  ensures forall j :: 0 <= j < |FilterEvens(s)| ==> IsEven(FilterEvens(s)[j])
{
  if |s| == 0 then
    []
  else
    var t := FilterEvens(s[..|s|-1]);
    if IsEven(s[|s|-1]) then t + [s[|s|-1]] else t
}

lemma FilterEvensUnfold(s: seq<int>)
  requires |s| > 0
  ensures FilterEvens(s) ==
            (if IsEven(s[|s|-1]) then FilterEvens(s[..|s|-1]) + [s[|s|-1]] else FilterEvens(s[..|s|-1]))
{
}

lemma FilterEvensExtend(s: seq<int>, x: int)
  ensures FilterEvens(s + [x]) == (if IsEven(x) then FilterEvens(s) + [x] else FilterEvens(s))
{
  if |s| == 0 {
    // s == []
    assert s + [x] == [x];
    // Unfold FilterEvens([x])
    FilterEvensUnfold([x]);
    assert [x][|[x]| - 1] == x;
    assert [x][..|[x]| - 1] == [];
    if IsEven(x) {
      assert FilterEvens([x]) == FilterEvens([]) + [x];
    } else {
      assert FilterEvens([x]) == FilterEvens([]);
    }
  } else {
    // Unfold FilterEvens(s + [x]) at the last element x
    FilterEvensUnfold(s + [x]);

    assert |s + [x]| == |s| + 1;
    assert (s + [x])[|s + [x]| - 1] == x;
    assert (s + [x])[..|s + [x]| - 1] == s;

    // Rewrite the unfolded form using the above facts
    if IsEven(x) {
      assert FilterEvens(s + [x]) == FilterEvens(s) + [x];
    } else {
      assert FilterEvens(s + [x]) == FilterEvens(s);
    }
  }
}

// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
  ensures evenList == FilterEvens(arr[..])
  ensures forall j :: 0 <= j < |evenList| ==> IsEven(evenList[j])
{
  evenList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant evenList == FilterEvens(arr[..i])
  {
    if IsEven(arr[i]) {
      evenList := evenList + [arr[i]];
    }

    // Help the invariant preservation step (from i to i+1)
    assert arr[..i+1] == arr[..i] + [arr[i]];
    FilterEvensExtend(arr[..i], arr[i]);
    if IsEven(arr[i]) {
      assert FilterEvens(arr[..i+1]) == FilterEvens(arr[..i]) + [arr[i]];
    } else {
      assert FilterEvens(arr[..i+1]) == FilterEvens(arr[..i]);
    }
  }

  // At loop exit, i == arr.Length, so arr[..i] is the full sequence
  assert arr[..arr.Length] == arr[..];
}

// Test cases checked statically.
method FindEvenNumbersTest() {
  // general case
  var a1 := new int[] [1, 2, 4];
  assert a1[..] == [1, 2, 4];
  var res1 := FindEvenNumbers(a1);
  assert res1 == [2, 4];

  // all even
  var a2 := new int[] [2, 4, 6];
  assert a2[..] == [2, 4, 6];
  var res2 := FindEvenNumbers(a2);
  assert res2 == [2, 4, 6];

  // none even
  var a3 := new int[] [1, 3, 5, 7];
  assert a3[..] == [1, 3, 5, 7];
  var res3 := FindEvenNumbers(a3);
  // Help Dafny compute FilterEvens([1,3,5,7]) == []
  assert !IsEven(1);
  assert !IsEven(3);
  assert !IsEven(5);
  assert !IsEven(7);

  // Connect literals with the "s + [x]" shape used by FilterEvensExtend
  assert [1] + [3] == [1, 3];
  assert [1, 3] + [5] == [1, 3, 5];
  assert [1, 3, 5] + [7] == [1, 3, 5, 7];

  FilterEvensExtend([], 1);
  assert FilterEvens([1]) == [];
  FilterEvensExtend([1], 3);
  assert FilterEvens([1, 3]) == [];
  FilterEvensExtend([1, 3], 5);
  assert FilterEvens([1, 3, 5]) == [];
  FilterEvensExtend([1, 3, 5], 7);
  assert FilterEvens([1, 3, 5, 7]) == [];
  assert res3 == [];

  // duplicates
  var a4 := new int[] [1, 2, 2, 3];
  assert a4[..] == [1, 2, 2, 3];
  var res4 := FindEvenNumbers(a4);
  // Help Dafny compute FilterEvens([1,2,2,3]) == [2,2]
  assert !IsEven(1);
  assert IsEven(2);
  assert !IsEven(3);

  // Connect literals with the "s + [x]" shape used by FilterEvensExtend
  assert [1] + [2] == [1, 2];
  assert [1, 2] + [2] == [1, 2, 2];
  assert [1, 2, 2] + [3] == [1, 2, 2, 3];

  FilterEvensExtend([], 1);
  assert FilterEvens([1]) == [];
  FilterEvensExtend([1], 2);
  assert FilterEvens([1, 2]) == [2];
  FilterEvensExtend([1, 2], 2);
  assert FilterEvens([1, 2, 2]) == [2, 2];
  FilterEvensExtend([1, 2, 2], 3);
  assert FilterEvens([1, 2, 2, 3]) == [2, 2];
  assert res4 == [2, 2];

  // empty
  var a5 := new int[] [];
  assert a5[..] == [];
  var res5 := FindEvenNumbers(a5);
  assert res5 == [];
}
