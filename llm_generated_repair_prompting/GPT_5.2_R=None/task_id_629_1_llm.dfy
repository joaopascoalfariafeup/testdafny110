// Retrives the sequence of even numbers from an array of integers.
method FindEvenNumbers(arr: array<int>) returns (evenList: seq<int>)
    ensures forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
    ensures forall i :: 0 <= i < arr.Length ==> (IsEven(arr[i]) ==> arr[i] in evenList)
    ensures multiset(evenList) == multiset(arr[..]).Elements({x => IsEven(x)})
{
    evenList := [];
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
        invariant multiset(evenList) == multiset(arr[..i]).Elements({x => IsEven(x)})
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
