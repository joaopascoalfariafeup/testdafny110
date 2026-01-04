// Counts the number of true values in a boolean array 'a'.

function CountTrue(a: array<bool>): nat
  reads a
{
  (forall j :: 0 <= j < a.Length ==> if a[j] then 1 else 0) + 0
}

method CalcCountTrue(a: array<bool>) returns (count: nat)
  ensures count == CountTrue(a)
{
  count := 0;
  for i := 0 to a.Length
    invariant count == CountTrue(a[..i])
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

