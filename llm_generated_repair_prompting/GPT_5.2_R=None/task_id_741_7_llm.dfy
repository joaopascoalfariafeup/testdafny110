// Checks if all characters in a string are equal
// (i.e., it does not have two distinct characters).
method AllCharactersSame(s: string) returns (result: bool)
  ensures result <==> (|s| == 0 || forall i :: 0 <= i < |s| ==> s[i] == s[0])
{
  if |s| > 1 {
    var firstChar := s[0];
    for i := 1 to |s|-1
      invariant 1 <= i <= |s|
      invariant firstChar == s[0]
      // all characters strictly before i have been checked equal to firstChar
      invariant forall j :: 0 <= j < i ==> s[j] == firstChar
    {
      if s[i] != firstChar {
        // show postcondition for result == false
        assert |s| != 0;
        assert 0 <= i < |s| && s[i] != s[0];
        assert !(forall k :: 0 <= k < |s| ==> s[k] == s[0]);
        assert (|s| == 0 || forall k :: 0 <= k < |s| ==> s[k] == s[0]) == false;
        return false;
      }
    }
    // loop finished normally; for-loop semantics give i == |s|
    // invariant gives: forall j :: 0 <= j < |s| ==> s[j] == firstChar
    assert forall k :: 0 <= k < |s| ==> s[k] == firstChar;
    assert forall k :: 0 <= k < |s| ==> s[k] == s[0];
  } else {
    // |s| <= 1 implies property holds
    if |s| == 0 {
      assert |s| == 0;
    } else {
      assert |s| == 1;
      assert forall k :: 0 <= k < |s| ==> s[k] == s[0];
    }
  }
  return true;
}

// Test cases checked statically.
method AllCharactersSameTest(){
  var s1 := "axa";
  var r1 := AllCharactersSame(s1);
  assert s1[0] == 'a' && s1[1] == 'x' && s1[2] == 'a'; // help the verifier
  assert !r1;

  var r2 := AllCharactersSame("aa"); assert r2;
  var r3 := AllCharactersSame("a"); assert r3;
  var r4 := AllCharactersSame(""); assert r4;
}
