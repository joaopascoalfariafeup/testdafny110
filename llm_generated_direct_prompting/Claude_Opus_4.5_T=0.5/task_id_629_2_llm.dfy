// Ghost function to compute the sequence of even numbers from a sequence of integers.
ghost function EvenNumbersSeq(s: seq<int>): seq<int>
{
    if |s| == 0 then []
    else if IsEven(s[|s|-1]) then EvenNumbersSeq(s[..|s|-1]) + [s[|s|-1]]
    else EvenNumbersSeq(s[..|s|-1])
}

// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
    ensures evenList == EvenNumbersSeq(arr[..])
{
    evenList := [];
    for i := 0 to arr.Length
        invariant evenList == EvenNumbersSeq(arr[..i])
    {
        if IsEven(arr[i]) {
            evenList := evenList + [arr[i]];
        }
        assert arr[..i+1] == arr[..i] + [arr[i]];
    }    
    assert arr[..arr.Length] == arr[..];
}


// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}



// Test cases checked statically.
method {:fuel EvenNumbersSeq, 5} FindEvenNumbersTest(){
    // general case
    var a1 := new int[] [1, 2, 4];
    var res1 := FindEvenNumbers(a1);
    assert a1[..] == [1, 2, 4];
    assert res1 == [2, 4];

    // all even
    var a2 := new int[] [2, 4, 6];
    var res2 := FindEvenNumbers(a2);
    assert a2[..] == [2, 4, 6];
    assert res2 == [2, 4, 6];

    // none even
    var a3 := new int[] [1, 3, 5, 7];
    var res3 := FindEvenNumbers(a3);
    assert a3[..] == [1, 3, 5, 7];
    assert res3 == [];

    // duplicates
    var a4 := new int[] [1, 2, 2, 3];
    var res4 := FindEvenNumbers(a4);
    assert a4[..] == [1, 2, 2, 3];
    assert res4 == [2, 2];

    // empty
    var a5 := new int[] [];
    var res5 := FindEvenNumbers(a5);
    assert a5[..] == [];
    assert res5 == [];
}
