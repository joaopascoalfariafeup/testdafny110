
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
        // The last element of s1+s2 is the last element of s2 if s1 is empty, but here s1 is non-empty
        // Actually, when s1 is non-empty, the last element of s1+s2 is the last element of s1
        // because s2 is appended after s1
        assert |s1| > 0;
        assert (s1 + s2)[|s1 + s2|-1] == (s1 + s2)[|s1|-1 + |s2|];
        assert (s1 + s2)[|s1|-1 + |s2|] == s2[|s2|-1] if |s1|-1 >= |s1| else s1[|s1|-1];
        // Actually simpler: when s1 is non-empty, the last element of s1+s2 is:
        // if |s2| == 0 then last element of s1 else last element of s2
        // But we need a more systematic approach
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

// Alternative simpler lemma that directly proves what we need for the postcondition
lemma sumNegativesAppendLemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sumNegatives(s[..i]) + sumNegatives(s[i..]) == sumNegatives(s)
  decreases i
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else {
    sumNegativesAppendLemma(s, i-1);
    // Now we know: sumNegatives(s[..(i-1)]) + sumNegatives(s[(i-1)..]) == sumNegatives(s)
    // We need to relate s[..i] and s[i..] to these
    assert s[..i] == s[..(i-1)] + [s[i-1]];
    assert s[i..] == s[(i-1)..][1..];
    // Calculate sumNegatives(s[..i])
    assert sumNegatives(s[..i]) == sumNegatives(s[..(i-1)]) + (if s[i-1] < 0 then s[i-1] else 0);
    // Calculate sumNegatives(s[(i-1)..])
    if |s[(i-1)..]| == 0 {
      // empty case
      assert s[(i-1)..] == [];
      assert s[i..] == [];
    } else {
      assert s[(i-1)..] == [s[i-1]] + s[i..];
      assert sumNegatives(s[(i-1)..]) == (if s[i-1] < 0 then s[i-1] else 0) + sumNegatives(s[i..]);
    }
    // Combine
    calc {
      sumNegatives(s[..i]) + sumNegatives(s[i..]);
      ==
      (sumNegatives(s[..(i-1)]) + (if s[i-1] < 0 then s[i-1] else 0)) + sumNegatives(s[i..]);
      ==
      sumNegatives(s[..(i-1)]) + ((if s[i-1] < 0 then s[i-1] else 0) + sumNegatives(s[i..]));
      == { assert (if s[i-1] < 0 then s[i-1] else 0) + sumNegatives(s[i..]) == sumNegatives(s[(i-1)..]); }
      sumNegatives(s[..(i-1)]) + sumNegatives(s[(i-1)..]);
      == { sumNegativesAppendLemma(s, i-1); }
      sumNegatives(s);
    }
  }
}

// Test cases checked statically.
method SumOfNegativesTest(){
  var a1 := new int[] [2, -6, -9];
  // Helper assertions to make the sequence concrete for Dafny
  assert a1[..] == [2, -6, -9];
  var out1 := CalcSumOfNegatives(a1);
  // Use the append lemma to help prove the test assertion
  sumNegativesAppendLemma([2, -6, -9], 3);
  assert sumNegatives([2, -6, -9]) == -15;
  assert out1 == -15;

  var a2 := new int[] [10, -14, 13];
  assert a2[..] == [10, -14, 13];
  var out2 := CalcSumOfNegatives(a2);
  // Use the append lemma to help prove the test assertion
  sumNegativesAppendLemma([10, -14, 13], 3);
  assert sumNegatives([10, -14, 13]) == -14;
  assert out2 == -14;
}




