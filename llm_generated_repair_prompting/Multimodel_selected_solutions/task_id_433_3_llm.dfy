// Helper lemma: turn 5 individual index facts into a quantified fact over the whole array
lemma ForallFromEnumeratedLen5(a: array<int>, n: int)
  requires a.Length == 5
  requires n > a[0] && n > a[1] && n > a[2] && n > a[3] && n > a[4]
  ensures  forall i :: 0 <= i < a.Length ==> n > a[i]
{
  forall i | 0 <= i < a.Length
    ensures n > a[i]
  {
    if i == 0 {
    } else if i == 1 {
    } else if i == 2 {
    } else if i == 3 {
    } else {
      assert i == 4; // since 0 <= i < 5 and i is not 0..3
    }
  }
}

// Checks if a number 'n' is greater than all elements in an array 'a'
method IsGreater(n: int, a: array<int>) returns (result: bool)
    ensures result <==> (forall i :: 0 <= i < a.Length ==> n > a[i])
{
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> n > a[j]
    {
        if n <= a[i] {
            return false;
        }
    }
    return true;
}

// Test cases checked statically
method IsGreaterTest(){
    var a1 := new int[] [3, 2, 1, 5, 2];

    // Help Dafny reason about the concrete contents of the array
    assert a1[..] == [3, 2, 1, 5, 2];
    assert a1.Length == 5;
    assert a1[0] == 3;
    assert a1[1] == 2;
    assert a1[2] == 1;
    assert a1[3] == 5;
    assert a1[4] == 2;

    var out1 := IsGreater(4, a1);
    assert out1 <==> (forall i :: 0 <= i < a1.Length ==> 4 > a1[i]);
    assert 0 <= 3 < a1.Length;
    assert !(4 > a1[3]); // since a1[3] == 5
    assert !(forall i :: 0 <= i < a1.Length ==> 4 > a1[i]);
    assert !out1;

    var out2 := IsGreater(6, a1);
    assert out2 <==> (forall i :: 0 <= i < a1.Length ==> 6 > a1[i]);
    ForallFromEnumeratedLen5(a1, 6);
    assert (forall i :: 0 <= i < a1.Length ==> 6 > a1[i]);
    assert out2;
}
