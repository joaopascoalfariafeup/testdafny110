
// Auxiliary function that preserves the order of elements
ghost function seqc<T,U>(s: seq<T>, f: T -> bool, g: T -> U): seq<U> 
{
  if s == [] then []
  else if f(s[|s|-1]) then seqc(s[..|s|-1], f, g) + [g(s[|s|-1])]
  else seqc(s[..|s|-1], f, g)
}

// Identity function
function id<T>(x: T): T { x }

// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Retrieves the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
  ensures evenList == seqc(arr[..], IsEven, id)
{
    evenList := [];
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant evenList == seqc(arr[..i], IsEven, id)
    {
        if i < arr.Length && IsEven(arr[i]) {
            evenList := evenList + [arr[i]];
            assert evenList == seqc(arr[..i+1], IsEven, id); // helper assertion
        }
    }    
}

// Test cases checked statically.
method FindEvenNumbersTest(){
    // general case
    var a1 := new int[] [1, 2, 4];
    var res1 := FindEvenNumbers(a1);
    assert a1[..] == [1, 2, 4]; // helper
    assert res1 == [2, 4];

    // all even
    var a2 := new int[] [2, 4, 6];
    var res2 := FindEvenNumbers(a2);
    assert a2[..] == [2, 4, 6]; // helper
    assert res2 == [2, 4, 6];

    // none even
    var a3 := new int[] [1, 3, 5, 7];
    var res3 := FindEvenNumbers(a3);
    assert a3[..] == [1, 3, 5, 7]; // helper
    assert res3 == [];

    // duplicates
    var a4 := new int[] [1, 2, 2, 3];
    var res4 := FindEvenNumbers(a4);
    assert a4[..] == [1, 2, 2, 3]; // helper
    assert res4 == [2, 2];

    // empty
    var a5 := new int[] [];
    var res5 := FindEvenNumbers(a5);
    assert a5[..] == []; // helper
    assert res5 == [];
}

