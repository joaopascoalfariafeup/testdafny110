// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
  ensures evenList == EvenPrefix(arr, arr.Length)
{
    evenList := [];
    for i := 0 to arr.Length
      invariant 0 <= i <= arr.Length
      invariant evenList == EvenPrefix(arr, i)
    {
        if IsEven(arr[i]) {
            evenList := evenList + [arr[i]];
            EvenPrefixExtend(arr, i);
            assert evenList == EvenPrefix(arr, i + 1);
        } else {
            EvenPrefixExtend(arr, i);
            assert evenList == EvenPrefix(arr, i + 1);
        }
    }    
}


function EvenPrefix(arr: array<int>, n: int): seq<int>
  requires 0 <= n <= arr.Length
  reads arr
  decreases n
{
  if n == 0 then []
  else
    EvenPrefix(arr, n - 1) +
    (if IsEven(arr[n - 1]) then [arr[n - 1]] else [])
}

lemma EvenPrefixExtend(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  ensures EvenPrefix(arr, i + 1) == EvenPrefix(arr, i) + (if IsEven(arr[i]) then [arr[i]] else [])
{
}


// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}



// Test cases checked statically.
method FindEvenNumbersTest(){
    // general case
    var a1 := new int[] [1, 2, 4];
    var res1 := FindEvenNumbers(a1);
    assert res1 == [2, 4];

    // all even
    var a2 := new int[] [2, 4, 6];
    var res2 := FindEvenNumbers(a2);
    assert res2 == [2, 4, 6];

    // none even
    var a3 := new int[] [1, 3, 5, 7];
    var res3 := FindEvenNumbers(a3);
    assert res3 == [];

    // duplicates
    var a4 := new int[] [1, 2, 2, 3];
    var res4 := FindEvenNumbers(a4);
    assert res4 == [2, 2];

    // empty
    var a5 := new int[] [];
    var res5 := FindEvenNumbers(a5);
    assert res5 == [];
}
