
// Iterative implementatiom.
// Returns the sum of the negative numbers in an array 'a'.  
method CalcSumOfNegatives(a: array<int>) returns (result: int)
  ensures result == sumNegatives(a[..])
{
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sumNegatives(a[..i])
  {
    if a[i] < 0 {
      result := result + a[i];
    }
    i := i + 1;
    // Helper assertion to maintain the invariant
    assert a[..i] == a[..i-1] + [a[i-1]];
    // Additional helper to connect sumNegatives
    assert sumNegatives(a[..i]) == sumNegatives(a[..i-1]) + (if a[i-1] < 0 then a[i-1] else 0);
  }
}

function sumNegatives(s: seq<int>): int
  decreases |s|
  ensures |s| == 0 ==> sumNegatives(s) == 0
  ensures |s| > 0 ==> sumNegatives(s) == (if s[|s|-1] < 0 then s[|s|-1] else 0) + sumNegatives(s[..|s|-1])
{
  if |s| == 0 then 0
  else (if s[|s|-1] < 0 then s[|s|-1] else 0) + sumNegatives(s[..|s|-1])
}

// Add a lemma to prove the distributive property separately
lemma sumNegativesDistributive(s1: seq<int>, s2: seq<int>)
  ensures sumNegatives(s1 + s2) == sumNegatives(s1) + sumNegatives(s2)
  decreases |s1|
{
  if |s1| == 0 {
    // Base case
    assert s1 + s2 == s2;
    assert sumNegatives(s1) == 0;
  } else {
    // Inductive step
    var last := s1[|s1|-1];
    var rest := s1[..|s1|-1];
    calc {
      sumNegatives(s1 + s2);
      == // by definition of sumNegatives
      (if (s1 + s2)[|s1 + s2|-1] < 0 then (s1 + s2)[|s1 + s2|-1] else 0) + sumNegatives((s1 + s2)[..|s1 + s2|-1]);
      == { 
        assert |s1 + s2| == |s1| + |s2|;
        assert (s1 + s2)[|s1 + s2|-1] == last;
        assert (s1 + s2)[..|s1 + s2|-1] == rest + s2;
      }
      (if last < 0 then last else 0) + sumNegatives(rest + s2);
      == { sumNegativesDistributive(rest, s2); }
      (if last < 0 then last else 0) + sumNegatives(rest) + sumNegatives(s2);
      == { 
        assert sumNegatives(s1) == (if last < 0 then last else 0) + sumNegatives(rest);
      }
      sumNegatives(s1) + sumNegatives(s2);
    }
  }
}

// Test cases checked statically.
method SumOfNegativesTest(){
  var a1 := new int[] [2, -6, -9];
  // Helper assertions to make the sequence concrete for Dafny
  assert a1[..] == [2, -6, -9];
  var out1 := CalcSumOfNegatives(a1);
  // Use lemma to help prove the test assertion
  sumNegativesDistributive([2, -6], [-9]);
  sumNegativesDistributive([2], [-6]);
  assert out1 == -15;

  var a2 := new int[] [10, -14, 13];
  assert a2[..] == [10, -14, 13];
  var out2 := CalcSumOfNegatives(a2);
  // Use lemma to help prove the test assertion
  sumNegativesDistributive([10, -14], [13]);
  sumNegativesDistributive([10], [-14]);
  assert out2 == -14;
}


