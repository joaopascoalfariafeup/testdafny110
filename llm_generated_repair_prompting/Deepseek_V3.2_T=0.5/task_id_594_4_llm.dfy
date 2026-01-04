// Returns the difference between the first even and the first odd number in the array.
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && IsEven(a[i])
  requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
  ensures exists i :: 0 <= i < a.Length && IsEven(a[i]) && (forall j :: 0 <= j < i ==> !IsEven(a[j])) && a[i] == old(a)[i]
  ensures exists i :: 0 <= i < a.Length && IsOdd(a[i]) && (forall j :: 0 <= j < i ==> !IsOdd(a[j])) && a[i] == old(a)[i]
  ensures diff == (var iEven :| 0 <= iEven < a.Length && IsEven(a[iEven]) && (forall j :: 0 <= j < iEven ==> !IsEven(a[j])); 
                  var iOdd :| 0 <= iOdd < a.Length && IsOdd(a[iOdd]) && (forall j :: 0 <= j < iOdd ==> !IsOdd(a[j])); 
                  a[iEven] - a[iOdd])
{
    var firstEven: int := 0;
    var i := 0;
    while i < a.Length && !IsEven(a[i])
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsEven(a[j])
      invariant firstEven == 0
    {
        i := i + 1;
    }
    if i < a.Length {
        firstEven := i;
    }

    var firstOdd: int := 0;
    i := 0;
    while i < a.Length && !IsOdd(a[i])
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> !IsOdd(a[j])
      invariant firstOdd == 0
    {
        i := i + 1;
    }
    if i < a.Length {
        firstOdd := i;
    }

    return a[firstEven] - a[firstOdd];
}

// Auxiliary predicates
predicate IsEven(n: int) {
    n % 2 == 0
}
predicate IsOdd(n: int) {
    n % 2 != 0
}

// Test cases checked statically by Dafny.
method FirstEvenOddDifferenceTest(){
    var a1 := new int[] [1, 3, 5, 7, 4, 1, 6, 8];
    // Prove preconditions for a1
    assert exists i :: 0 <= i < a1.Length && IsEven(a1[i]) by {
        assert IsEven(a1[4]); // 4 is even
    }
    assert exists i :: 0 <= i < a1.Length && IsOdd(a1[i]) by {
        assert IsOdd(a1[0]); // 1 is odd
    }
    var out1 := FirstEvenOddDifference(a1);
    assert out1 == 3;

    var a2 := new int[] [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    // Prove preconditions for a2
    assert exists i :: 0 <= i < a2.Length && IsEven(a2[i]) by {
        assert IsEven(a2[1]); // 2 is even
    }
    assert exists i :: 0 <= i < a2.Length && IsOdd(a2[i]) by {
        assert IsOdd(a2[0]); // 1 is odd
    }
    var out2 := FirstEvenOddDifference(a2);
    assert out2 == 1;

    var a3:= new int[] [1, 5, 7, 9, 10];
    // Prove preconditions for a3
    assert exists i :: 0 <= i < a3.Length && IsEven(a3[i]) by {
        assert IsEven(a3[4]); // 10 is even
    }
    assert exists i :: 0 <= i < a3.Length && IsOdd(a3[i]) by {
        assert IsOdd(a3[0]); // 1 is odd
    }
    var out3 := FirstEvenOddDifference(a3);
    assert out3 == 9;
}



