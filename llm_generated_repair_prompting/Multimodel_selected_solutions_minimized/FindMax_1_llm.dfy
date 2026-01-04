// Finds the maximum value in a non-empty array.
method FindMax(a: array<real>) returns (max: real)
    requires a.Length > 0
    ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
    ensures exists k :: 0 <= k < a.Length && max == a[k]
{
    max := a[0];
    for i := 1 to a.Length
        invariant forall k :: 0 <= k < i ==> max >= a[k]
        invariant exists k :: 0 <= k < i && max == a[k]
    {
        if (a[i] > max) {
            max := a[i];
        }
    } 
}

// Test cases checked statically.
method testFindMax() {
    var a1 := new real[3] [2.0, 3.0, 1.0]; // normal
    var m1 := FindMax(a1);
  
    var a2 := new real[3] [1.0, 2.0, 2.0]; // duplicates
    var m2 := FindMax(a2);
    assert m2 == a2[1] == 2.0;

    var a3 := new real[1] [1.0]; // single element
    var m3 := FindMax(a3);
    assert m3 == a3[0] == 1.0;

    var a4 := new real[3] [1.0, 1.0, 1.0]; // all equal
    var m4 := FindMax(a4);
    assert m4 == a4[0] == 1.0;    
}
