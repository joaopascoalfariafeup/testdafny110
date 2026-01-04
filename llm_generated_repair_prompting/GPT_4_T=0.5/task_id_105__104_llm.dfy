
ghost function {:fuel a} CountTrue(a: seq<bool>, end: nat): nat
  requires end <= |a|
{
  if end == 0 then 0
  else CountTrue(a[..end-1], end-1) + (if a[end-1] then 1 else 0)
}

method CalcCountTrue(a: array<bool>) returns (count: nat)
  requires a != null
  ensures count == CountTrue(a[..], a.Length)
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountTrue(a[..i], i)
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
  assert a1[0] == true && a1[1] == false && a1[2] == true; // alternative helper 
  assert c1 == 2;
 
  var a2 := new bool[] [false, false];
  assert a2[..] == [false, false]; // helper
  var c2 := CalcCountTrue(a2);
  assert a2[0] == false && a2[1] == false; // alternative helper 
  assert c2 == 0;

  var a3 := new bool[] [true, true, true];
  assert a3[..] == [true, true, true]; // helper
  var c3 := CalcCountTrue(a3);
  assert a3[0] == true && a3[1] == true && a3[2] == true; // alternative helper 
  assert c3 == 3;
}


