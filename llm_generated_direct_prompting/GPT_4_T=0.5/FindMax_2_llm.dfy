// Auxiliary function to find the maximum value in a sequence.
ghost function SeqMax(s: seq<real>): real
  requires |s| > 0
{
  if |s| == 1 then s[0] else max(s[0], SeqMax(s[1..]))
}

// Finds the maximum value in a non-empty array.
method FindMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures max == SeqMax(a[..])
{
    max := a[0];
    for i := 1 to a.Length
      invariant 0 <= i <= a.Length
      invariant max == SeqMax(a[..i])
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
    assert m1 == SeqMax(a1[..]);

    var a2 := new real[3] [1.0, 2.0, 2.0]; // duplicates
    var m2 := FindMax(a2);
    assert m2 == SeqMax(a2[..]);

    var a3 := new real[1] [1.0]; // single element
    var m3 := FindMax(a3);
    assert m3 == SeqMax(a3[..]);

    var a4 := new real[3] [1.0, 1.0, 1.0]; // all equal
    var m4 := FindMax(a4);
    assert m4 == SeqMax(a4[..]);    
}
