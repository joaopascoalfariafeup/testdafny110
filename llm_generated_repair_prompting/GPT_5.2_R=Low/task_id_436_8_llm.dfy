// Returns a sequence with the negative numbers in the input sequence 's',
// in the same order as they appear in the sequence.
function {:opaque} Negatives(s: seq<int>): seq<int>
{
  if |s| == 0 then
    []
  else
    Negatives(s[..|s|-1]) + (if s[|s|-1] < 0 then [s[|s|-1]] else [])
}

// Rewrite/base lemma for faster proof search
lemma {:rewrite} NegativesNil()
  ensures Negatives([]) == []
{
  reveal Negatives;
}

// Negatives of an empty prefix is empty (helps loop-invariant initialization)
lemma {:rewrite} NegativesTake0(s: seq<int>)
  ensures Negatives(s[..0]) == []
{
  assert s[..0] == [];
  NegativesNil();
}

// Helper lemma: Negatives distributes over appending one element
lemma {:rewrite} NegativesSnoc(s: seq<int>, x: int)
  ensures Negatives(s + [x]) == Negatives(s) + (if x < 0 then [x] else [])
{
  // Facts needed for unfolding Negatives on (s + [x])
  assert |s + [x]| == |s| + 1;
  assert |s + [x]| - 1 == |s|;
  assert (s + [x])[..|s|] == s;
  assert (s + [x])[|s + [x]| - 1] == x;

  reveal Negatives;

  calc {
    Negatives(s + [x]);
    ==
      Negatives((s + [x])[..|s + [x]| - 1]) +
        (if (s + [x])[|s + [x]| - 1] < 0 then [(s + [x])[|s + [x]| - 1]] else []);
    ==
      Negatives((s + [x])[..|s|]) + (if x < 0 then [x] else []);
    ==
      Negatives(s) + (if x < 0 then [x] else []);
  }
}

// Convenience: singleton case (helps tests simplify faster)
lemma {:rewrite} NegativesSingleton(x: int)
  ensures Negatives([x]) == (if x < 0 then [x] else [])
{
  assert [] + [x] == [x];
  NegativesSnoc([], x);
  NegativesNil();
  calc {
    Negatives([x]);
    ==
      Negatives([] + [x]);
    ==
      Negatives([]) + (if x < 0 then [x] else []);
    ==
      [] + (if x < 0 then [x] else []);
    ==
      (if x < 0 then [x] else []);
  }
}

method FindNegativeNumbers(a: array<int>) returns (res: seq<int>)
  ensures res == Negatives(a[..a.Length])
{
  res := [];

  // Establish loop invariant for i == 0
  NegativesTake0(a[..a.Length]);
  assert res == Negatives(a[..0]);

  for i := 0 to a.Length
    invariant 0 <= i <= a.Length
    invariant res == Negatives(a[..i])
  {
    ghost var r0 := res;

    if a[i] < 0 {
      res := res + [a[i]];
      assert res == r0 + [a[i]];
    } else {
      assert res == r0;
    }

    // Show invariant for next i (i becomes i+1 after the iteration)
    assert a[..i+1] == a[..i] + [a[i]];
    NegativesSnoc(a[..i], a[i]);
    assert Negatives(a[..i+1]) == Negatives(a[..i]) + (if a[i] < 0 then [a[i]] else []);
    assert res == Negatives(a[..i+1]);
  }
}


// Test cases checked statically.
method {:timeLimit 120} FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  assert a1[..] == [-1, 4, 5, -6];
  assert a1[..a1.Length] == a1[..];
  var res1 := FindNegativeNumbers(a1);
  assert res1 == Negatives(a1[..a1.Length]);
  assert Negatives(a1[..a1.Length]) == Negatives([-1, 4, 5, -6]);
  // Compute Negatives([-1,4,5,-6]) by successive snoc steps
  NegativesSnoc([], -1);
  NegativesNil();
  assert [] + [-1] == [-1];
  NegativesSingleton(-1);
  assert Negatives([-1]) == [-1];

  NegativesSnoc([-1], 4);
  assert [-1] + [4] == [-1, 4];
  assert Negatives([-1, 4]) == [-1];

  NegativesSnoc([-1, 4], 5);
  assert [-1, 4] + [5] == [-1, 4, 5];
  assert Negatives([-1, 4, 5]) == [-1];

  NegativesSnoc([-1, 4, 5], -6);
  assert [-1, 4, 5] + [-6] == [-1, 4, 5, -6];
  assert Negatives([-1, 4, 5, -6]) == [-1, -6];
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  assert a2[..] == [-1, -2, -3];
  assert a2[..a2.Length] == a2[..];
  var res2 := FindNegativeNumbers(a2);
  assert res2 == Negatives(a2[..a2.Length]);
  assert Negatives(a2[..a2.Length]) == Negatives([-1, -2, -3]);
  NegativesSnoc([], -1);
  NegativesNil();
  assert [] + [-1] == [-1];
  NegativesSingleton(-1);
  assert Negatives([-1]) == [-1];

  NegativesSnoc([-1], -2);
  assert [-1] + [-2] == [-1, -2];
  assert Negatives([-1, -2]) == [-1, -2];

  NegativesSnoc([-1, -2], -3);
  assert [-1, -2] + [-3] == [-1, -2, -3];
  assert Negatives([-1, -2, -3]) == [-1, -2, -3];
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  assert a3[..] == [0, 1];
  assert a3[..a3.Length] == a3[..];
  var res3 := FindNegativeNumbers(a3);
  assert res3 == Negatives(a3[..a3.Length]);
  assert Negatives(a3[..a3.Length]) == Negatives([0, 1]);
  NegativesSnoc([], 0);
  NegativesNil();
  assert [] + [0] == [0];
  NegativesSingleton(0);
  assert Negatives([0]) == [];
  NegativesSnoc([0], 1);
  assert [0] + [1] == [0, 1];
  assert Negatives([0, 1]) == [];
  assert res3 == [];
}
