// Counts the number of true values in a boolean array 'a'.

ghost function CountTrue(a: array<bool>, end: nat): nat
  requires end <= a.Length
  reads a
{
  if end == 0 then 0
  else CountTrue(a, end-1) + (if a[end-1] then 1 else 0)
}

ghost function CountTrueUpTo(a: array<bool>, end: nat): nat
  requires end <= a.Length
  reads a
{
  if end == 0 then 0
  else CountTrueUpTo(a, end-1) + (if a[end-1] then 1 else 0)
}

method CalcCountTrue(a: array<bool>) returns (count: nat)
  ensures count == CountTrue(a, a.Length)
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountTrueUpTo(a, i)
  {
    if a[i] {
      count := count + 1;
    }
  }
}

// Test cases checked statically.
method CountTrueTest(){
  var a1 := new bool[] [true, false, true];
  assert a1[..] == [true, false, true]; // helper
  var c1 := CalcCountTrue(a1);
  assert c1 == 2;
 
  var a2 := new bool[] [false, false];
  assert a2[..] == [false, false]; // helper
  var c2 := CalcCountTrue(a2);
  assert c2 == 0;

  var a3 := new bool[] [true, true, true];
  assert a3[..] == [true, true, true]; // helper
  var c3 := CalcCountTrue(a3);
  assert c3 == 3;
}
