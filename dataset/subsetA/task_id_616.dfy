// Given two arrays of integers, a and b (without zeros), of the same length, 
// return an array of the same length, where each element is the remainder 
// of the corresponding element in 'a' divided by the corresponding element in 'b'.
method ElementWiseModulo(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> b[i] != 0
    ensures fresh(result)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[i] % b[i]
{
    result := new int[a.Length];
    for i := 0 to a.Length
        invariant forall k :: 0 <= k < i ==> result[k] == a[k] % b[k]
    {
        result[i] := a[i] % b[i];
    }
}

// Test cases checked statically.
method ElementWiseModuloTest(){
    var a1:= new int[] [10, 4, 5, 6];
    var a2:= new int[] [5, 6, 7, 5];
    var res1 := ElementWiseModulo(a1, a2);
    assert res1[..] == [0, 4, 5, 1];

    var a3:= new int[] [11, 5, 6, 7];
    var a4:= new int[] [6, 7, 8, 6];
    var res2 := ElementWiseModulo(a3, a4);
    assert res2[..] == [5, 5, 6, 1];
}

