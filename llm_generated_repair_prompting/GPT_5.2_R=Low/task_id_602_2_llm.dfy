// Finds the first repeated character in a string. Returns a pair (found, c) where
// found is true if a repeated character was found, and c is the repeated character.

predicate HasRepeatAt(s: string, i: int)
{
  0 <= i < |s| &&
  exists j :: i < j < |s| && s[i] == s[j]
}

predicate NoRepeatBefore(s: string, i: int)
{
  0 <= i <= |s| &&
  forall k :: 0 <= k < i ==> !HasRepeatAt(s, k)
}

predicate FirstRepeatedChar(s: string, c: char)
{
  exists i :: 0 <= i < |s| && s[i] == c && HasRepeatAt(s, i) && NoRepeatBefore(s, i)
}

predicate Unique(s: string)
{
  forall k :: 0 <= k < |s| ==> !HasRepeatAt(s, k)
}

// The "first repeated char" is unique (if it exists).
lemma FirstRepeatedCharUnique(s: string, c1: char, c2: char)
  requires FirstRepeatedChar(s, c1)
  requires FirstRepeatedChar(s, c2)
  ensures c1 == c2
{
  var i1 :| 0 <= i1 < |s| && s[i1] == c1 && HasRepeatAt(s, i1) && NoRepeatBefore(s, i1);
  var i2 :| 0 <= i2 < |s| && s[i2] == c2 && HasRepeatAt(s, i2) && NoRepeatBefore(s, i2);

  if i1 < i2 {
    // NoRepeatBefore(s,i2) forbids any repeat at positions < i2, including i1
    assert !HasRepeatAt(s, i1);
    assert HasRepeatAt(s, i1);
    assert false;
  } else if i2 < i1 {
    assert !HasRepeatAt(s, i2);
    assert HasRepeatAt(s, i2);
    assert false;
  } else {
    assert i1 == i2;
  }

  assert s[i1] == c1;
  assert s[i2] == c2;
  assert i1 == i2;
  assert c1 == c2;
}

method FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> FirstRepeatedChar(s, c)
  ensures !found ==> Unique(s)
{
    found := false;

    // scan the string from left to right (until a repeated character is found)
    for i := 0 to |s|
      invariant 0 <= i <= |s|
      invariant forall k :: 0 <= k < i ==> !HasRepeatAt(s, k)
    {
        // check if the character is repeated in the subsequent positions
        for j := i + 1 to |s|
          invariant i + 1 <= j <= |s|
          invariant forall t :: i + 1 <= t < j ==> s[i] != s[t]
        {
            if s[i] == s[j] {
                assert HasRepeatAt(s, i);
                assert NoRepeatBefore(s, i);
                assert FirstRepeatedChar(s, s[i]);
                return true, s[i];
            }
        }
        assert !HasRepeatAt(s, i);
    }
    assert Unique(s);
    return false, ' ';
}

// Test cases checked statically by Dafny.
method FindFirstRepeatedCharTest(){
    // First character is repeated
    var s1 := "abcabc";
    var found1, out1 := FindFirstRepeatedChar(s1);

    // Prove s1 is not unique, hence found1 must be true (using postcondition contrapositive)
    assert HasRepeatAt(s1, 0); // witness j=3 exists
    assert !Unique(s1);
    if !found1 {
      assert Unique(s1); // from method postcondition
      assert false;
    }
    assert found1;

    // Prove the expected "first repeated" character is 'a', and use uniqueness to get out1 == 'a'
    assert FirstRepeatedChar(s1, 'a'); // i=0 works; NoRepeatBefore vacuous
    assert FirstRepeatedChar(s1, out1); // from method postcondition since found1
    FirstRepeatedCharUnique(s1, out1, 'a');
    assert out1 == 'a';
    assert found1 && out1 == 'a';

    // Middle character is repeated
    var s2 := "axbcx";
    var found2, out2 := FindFirstRepeatedChar(s2);

    // Show s2 is not unique (repeat at i=1 with j=4), hence found2
    assert HasRepeatAt(s2, 1);
    assert !Unique(s2);
    if !found2 {
      assert Unique(s2);
      assert false;
    }
    assert found2;

    // Show 'x' is the first repeated character:
    // need NoRepeatBefore(s2,1), i.e., !HasRepeatAt(s2,0)
    if HasRepeatAt(s2, 0) {
      var j :| 0 < j < |s2| && s2[0] == s2[j];
      assert j == 1 || j == 2 || j == 3 || j == 4;
      // s2 = "a x b c x"
      assert s2[0] == 'a';
      assert s2[1] == 'x';
      assert s2[2] == 'b';
      assert s2[3] == 'c';
      assert s2[4] == 'x';
      if j == 1 { assert s2[0] != s2[1]; }
      if j == 2 { assert s2[0] != s2[2]; }
      if j == 3 { assert s2[0] != s2[3]; }
      if j == 4 { assert s2[0] != s2[4]; }
      assert false;
    }
    assert !HasRepeatAt(s2, 0);
    assert NoRepeatBefore(s2, 1);

    assert FirstRepeatedChar(s2, 'x'); // i=1
    assert FirstRepeatedChar(s2, out2); // from method postcondition since found2
    FirstRepeatedCharUnique(s2, out2, 'x');
    assert out2 == 'x';
    assert found2 && out2 == 'x';

    // No repeated characters
    var s4 := "123456";
    var found4, out4 := FindFirstRepeatedChar(s4);
    assert !found4;
}

