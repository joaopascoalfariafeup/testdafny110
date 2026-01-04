// Checks if a number 'n' is greater than all elements in an array 'a'
method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result <==> (forall i :: 0 <= i < a.Length ==> n > a[i])
{
    var resultLocal := true;

    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant resultLocal <==> (forall j :: 0 <= j < i ==> n > a[j])
    {
        if n <= a[i] {
            resultLocal := false;
            break;
        }
    }
    return resultLocal;
}

// Test cases checked statically
method IsGreaterTest(){
    var a1 := new int[] [3, 2, 1, 5, 2];
    assert a1[..] == [3, 2, 1, 5, 2];

    var out1 := IsGreater(4, a1);
    assert !out1;

    var out2 := IsGreater(6, a1);
    assert out2;
}
