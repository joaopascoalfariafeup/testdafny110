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
    var i := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
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
        i := i + 1;
    }    
}

// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Auxiliary ghost function for ordering preservation
ghost function {:fuel 5} seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
  ensures |seqc(s, f, g)| <= |s|
  ensures forall k :: 0 <= k < |s| && f(s[k]) ==> g(s[k]) in seqc(s, f, g)
  ensures forall y :: y in seqc(s, f, g) ==> exists k :: 0 <= k < |s| && f(s[k]) && g(s[k]) == y
  // Simplified ordering preservation: maintains relative order
  ensures forall i, j :: 0 <= i < j < |s| && f(s[i]) && f(s[j]) ==> 
    exists p, q :: 0 <= p < q < |seqc(s, f, g)| && seqc(s, f, g)[p] == g(s[i]) && seqc(s, f, g)[q] == g(s[j])
{
  if s == [] then []
  else 
    var prev := seqc(s[..|s|-1], f, g);
    if f(s[|s|-1]) then prev + [g(s[|s|-1])]
    else prev
}

// Test cases checked statically.
method FindEvenNumbersTest(){
    // general case
    var a1 := new int[] [1, 2, 4];
    // Add helper assertions to help Dafny understand array contents
    assert a1[..] == [1, 2, 4];
    var res1 := FindEvenNumbers(a1);
    // Add lemma to help prove ordering
    assert seqc([1,2,4], IsEven, (x: int) => x) == [2,4];
    assert res1 == [2, 4];

    // all even
    var a2 := new int[] [2, 4, 6];
    assert a2[..] == [2, 4, 6];
    var res2 := FindEvenNumbers(a2);
    assert seqc([2,4,6], IsEven, (x: int) => x) == [2,4,6];
    assert res2 == [2, 4, 6];

    // none even
    var a3 := new int[] [1, 3, 5, 7];
    assert a3[..] == [1, 3, 5, 7];
    var res3 := FindEvenNumbers(a3);
    assert seqc([1,3,5,7], IsEven, (x: int) => x) == [];
    assert res3 == [];

    // duplicates
    var a4 := new int[] [1, 2, 2, 3];
    assert a4[..] == [1, 2, 2, 3];
    var res4 := FindEvenNumbers(a4);
    assert seqc([1,2,2,3], IsEven, (x: int) => x) == [2,2];
    assert res4 == [2, 2];

    // empty
    var a5 := new int[] [];
    assert a5[..] == [];
    var res5 := FindEvenNumbers(a5);
    assert seqc([], IsEven, (x: int) => x) == [];
    assert res5 == [];
}







