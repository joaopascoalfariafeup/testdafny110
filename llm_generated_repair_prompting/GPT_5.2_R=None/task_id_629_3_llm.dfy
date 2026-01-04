// Predicate that checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Multiset of elements of a sequence that satisfy a predicate
ghost function MSFilter<T>(s: seq<T>, p: T -> bool): multiset<T>
{
  if |s| == 0 then multiset{}
  else
    var ms := MSFilter(s[..|s|-1], p);
    if p(s[|s|-1]) then ms + multiset{s[|s|-1]} else ms
}

// Ghost function: filters a sequence, preserving order
ghost function FilterEven(s: seq<int>): seq<int>
  ensures forall k :: 0 <= k < |FilterEven(s)| ==> IsEven(FilterEven(s)[k])
  ensures multiset(FilterEven(s)) == MSFilter(s, IsEven)
{
  if |s| == 0 then []
  else
    var t := FilterEven(s[..|s|-1]);
    if IsEven(s[|s|-1]) then t + [s[|s|-1]] else t
}

// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
  requires arr != null
  ensures evenList == FilterEven(arr[..])
  ensures forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
  ensures forall i :: 0 <= i < arr.Length ==> (IsEven(arr[i]) ==> arr[i] in evenList)
  ensures multiset(evenList) == MSFilter(arr[..], IsEven)
{
  evenList := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant evenList == FilterEven(arr[..i])
    invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
    invariant multiset(evenList) == MSFilter(arr[..i], IsEven)
  {
    if IsEven(arr[i]) {
      evenList := evenList + [arr[i]];
      assert arr[..i+1] == arr[..i] + [arr[i]];
    } else {
      assert arr[..i+1] == arr[..i] + [arr[i]];
    }
  }
}

// Test cases checked statically.
method FindEvenNumbersTest() {
  // general case
  var a1 := new int[] [1, 2, 4];
  assert a1[..] == [1,2,4];
  var res1 := FindEvenNumbers(a1);
  assert res1 == [2, 4];

  // all even
  var a2 := new int[] [2, 4, 6];
  assert a2[..] == [2,4,6];
  var res2 := FindEvenNumbers(a2);
  assert res2 == [2, 4, 6];

  // none even
  var a3 := new int[] [1, 3, 5, 7];
  assert a3[..] == [1,3,5,7];
  var res3 := FindEvenNumbers(a3);
  assert res3 == [];

  // duplicates
  var a4 := new int[] [1, 2, 2, 3];
  assert a4[..] == [1,2,2,3];
  var res4 := FindEvenNumbers(a4);
  assert res4 == [2, 2];

  // empty
  var a5 := new int[] [];
  assert a5[..] == [];
  var res5 := FindEvenNumbers(a5);
  assert res5 == [];
}
