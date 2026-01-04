// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
    ensures evenList == Filter(arr[..], IsEven)
{
    evenList := [];
    for i := 0 to arr.Length
        invariant evenList == Filter(arr[..i], IsEven)
    {
        if IsEven(arr[i]) {
            evenList := evenList + [arr[i]];
        }
        assert arr[..i+1] == arr[..i] + [arr[i]]; // proof helper
    }    
    assert arr[..] == arr[..arr.Length]; // proof helper
}

// Selects from a sequence the elements that satisfy a predicate.
ghost function {:fuel 5} Filter<T>(s: seq<T>, p: T -> bool) : seq<T> {
    if |s| == 0 then []
    else if p(Last(s)) then Filter(DropLast(s), p) + [Last(s)]
    else Filter(DropLast(s), p)
}

// Predicate that checks if a number is even.
predicate IsEven(n: int) {
    n % 2 == 0
}

// Helper functions for sequences
ghost function Last<T>(s: seq<T>) : T
    requires |s| > 0
{ 
    s[|s|-1] 
}

ghost function DropLast<T>(s: seq<T>) : seq<T>
    requires |s| > 0
{ 
    s[..|s|-1] 
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