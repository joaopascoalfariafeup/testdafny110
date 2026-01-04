// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
  ensures |evenList| <= arr.Length
  ensures forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
  ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
  ensures forall x :: x in evenList ==> x in arr[..] && IsEven(x)
  // Add ordering preservation postcondition
  ensures evenList == seqc(arr[..], IsEven, (x: int) => x)
{
    evenList := [];
    for i := 0 to arr.Length
      invariant |evenList| <= i
      invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
      invariant forall j :: 0 <= j < i && IsEven(arr[j]) ==> arr[j] in evenList
      invariant forall x :: x in evenList ==> x in arr[..] && IsEven(x)
      // Add ordering preservation invariant
      invariant evenList == seqc(arr[..i], IsEven, (x: int) => x)
    {
        if IsEven(arr[i]) {
            evenList := evenList + [arr[i]];
        }
    }    
}

// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Auxiliary ghost function for ordering preservation
ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
  else seqc(s[..|s|-1], f, g)
}

// Test cases checked statically.
method FindEvenNumbersTest(){
    // general case
    var a1 := new int[] [1, 2, 4];
    // Add helper assertions to help Dafny understand array contents
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
    assert res3 == [];

    // duplicates
    var a4 := new int[] [1, 2, 2, 3];
    assert a4[..] == [1, 2, 2, 3];
    var res4 := FindEvenNumbers(a4);
    assert res4 == [2, 2];

    // empty
    var a5 := new int[] [];
    assert a5[..] == [];
    var res5 := FindEvenNumbers(a5);
    assert res5 == [];
}

