// Counts the number of true values in a boolean array 'a'.
function CountTrue(s: seq<bool>): nat
{
  if |s| == 0 then 0 else CountTrue(s[..|s|-1]) + (if s[|s|-1] then 1 else 0)
}

method CalcCountTrue(a: array<bool>) returns (count: nat)
  ensures count == CountTrue(a[..])
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountTrue(a[..i])
  {
    if a[i] {
      count := count + 1;
    }
    assert count == CountTrue(a[..i+1]);
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

