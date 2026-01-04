// Counts the number of true values in a boolean array 'a'.
function {:fuel 10} CountTrue(s: seq<bool>): nat
{
  if |s| == 0 then 0
  else CountTrue(s[..|s|-1]) + (if s[|s|-1] then 1 else 0)
}

lemma CountTrueExtend(s: seq<bool>, b: bool)
  ensures CountTrue(s + [b]) == CountTrue(s) + (if b then 1 else 0)
{
  // Unfold CountTrue on (s+[b]) and simplify the prefix/last element.
  assert |s + [b]| == |s| + 1;
  assert (s + [b])[..|s|] == s;
  assert (s + [b])[|s|] == b;

  calc {
    CountTrue(s + [b]);
    == {
      assert |s + [b]| > 0;
    }
    CountTrue((s + [b])[..|s + [b]| - 1]) + (if (s + [b])[|s + [b]| - 1] then 1 else 0);
    == {
      assert |s + [b]| - 1 == |s|;
      assert (s + [b])[..|s + [b]| - 1] == (s + [b])[..|s|];
      assert (s + [b])[|s + [b]| - 1] == (s + [b])[|s|];
    }
    CountTrue((s + [b])[..|s|]) + (if (s + [b])[|s|] then 1 else 0);
    == { }
    CountTrue(s) + (if b then 1 else 0);
  }
}

method CalcCountTrue(a: array<bool>) returns (count: nat)
  ensures count == CountTrue(a[..])
{
  count := 0;
  for i := 0 to a.Length
    invariant 0 <= count <= i
    invariant count == CountTrue(a[..i])
  {
    if a[i] {
      count := count + 1;
      assert a[..(i+1)] == a[..i] + [a[i]];
      calc {
        CountTrue(a[..(i+1)]);
        == { CountTrueExtend(a[..i], a[i]); }
        CountTrue(a[..i]) + (if a[i] then 1 else 0);
        == { assert a[i]; }
        CountTrue(a[..i]) + 1;
        == { }
        count;
      }
    } else {
      assert a[..(i+1)] == a[..i] + [a[i]];
      calc {
        CountTrue(a[..(i+1)]);
        == { CountTrueExtend(a[..i], a[i]); }
        CountTrue(a[..i]) + (if a[i] then 1 else 0);
        == { assert !a[i]; }
        CountTrue(a[..i]);
        == { }
        count;
      }
    }
  }

  // Help Dafny relate a[..] to the explicit full slice a[..a.Length]
  assert a[..] == a[..a.Length];
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
