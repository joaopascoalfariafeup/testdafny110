// Counts the number of true values in a boolean array 'a'.
method CalcCountTrue(a: array<bool>) returns (count: nat)
  ensures count == |a| - (sum {i in a | !i}) // the count is equal to the length of the array minus the number of false values
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant count == i - (sum {j in 0..i | !a[j]}) // at any point in the loop, the count is equal to the current index minus the number of false values up to that index
  {
    if a[i] {
      count := count + 1;
    }
  }
}

// Test cases checked statically.
method CountTrueTest(){
  var a1 := new bool[] [true, false, true];
  var c1 := CalcCountTrue(a1);
  assert c1 == 2;
 
  var a2 := new bool[] [false, false];
  var c2 := CalcCountTrue(a2);
  assert c2 == 0;

  var a3 := new bool[] [true, true, true];
  var c3 := CalcCountTrue(a3);
  assert c3 == 3;
}

