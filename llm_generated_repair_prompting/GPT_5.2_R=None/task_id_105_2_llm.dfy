// Counts the number of true values in a boolean array 'a'.
method CalcCountTrue(a: array<bool>) returns (count: nat)
  requires a != null
  ensures count == (|set j | 0 <= j < a.Length && a[j]|)
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= count <= i
    invariant count == (|set j | 0 <= j < i && a[j]|)
  {
    if a[i] {
      // Help the verifier relate the old set to the new one
      assert (set j | 0 <= j < i + 1 && a[j]) ==
             (set j | 0 <= j < i && a[j]) + (if a[i] then {i} else {});
      count := count + 1;
    } else {
      // Help the verifier relate the sets when a[i] is false
      assert (set j | 0 <= j < i + 1 && a[j]) == (set j | 0 <= j < i && a[j]);
    }
  }
}

// Test cases checked statically.
method CountTrueTest(){
  var a1 := new bool[] [true, false, true];
  assert a1[..] == [true, false, true];
  var c1 := CalcCountTrue(a1);
  assert c1 == 2;
 
  var a2 := new bool[] [false, false];
  assert a2[..] == [false, false];
  var c2 := CalcCountTrue(a2);
  assert c2 == 0;

  var a3 := new bool[] [true, true, true];
  assert a3[..] == [true, true, true];
  var c3 := CalcCountTrue(a3);
  assert c3 == 3;
}
