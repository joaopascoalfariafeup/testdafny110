// Replace all occurrences of oldChar in string s by newChar 
// and return the resulting string.
function ReplaceSeq(s: seq<char>, oldChar: char, newChar: char): seq<char>
{
  if |s| == 0 then []
  else
    ReplaceSeq(s[..|s|-1], oldChar, newChar) +
    [if s[|s|-1] == oldChar then newChar else s[|s|-1]]
}

// Helpful lemma for one-step extension (snoc) of ReplaceSeq
lemma ReplaceSeqSnoc(t: seq<char>, c: char, oldChar: char, newChar: char)
  ensures ReplaceSeq(t + [c], oldChar, newChar)
        == ReplaceSeq(t, oldChar, newChar) + [if c == oldChar then newChar else c]
{
  assert |t + [c]| == |t| + 1;
  assert (t + [c])[..|t|] == t;
  assert (t + [c])[|t|] == c;

  calc {
    ReplaceSeq(t + [c], oldChar, newChar);
    == {
    }
    ReplaceSeq((t + [c])[..|(t + [c])| - 1], oldChar, newChar)
      + [if (t + [c])[|(t + [c])| - 1] == oldChar then newChar else (t + [c])[|(t + [c])| - 1]];
    == {
      assert |(t + [c])| - 1 == |t|;
    }
    ReplaceSeq((t + [c])[..|t|], oldChar, newChar)
      + [if (t + [c])[|t|] == oldChar then newChar else (t + [c])[|t|]];
    == {
    }
    ReplaceSeq(t, oldChar, newChar) + [if c == oldChar then newChar else c];
  }
}

method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
  ensures |v| == |s|
  ensures v == ReplaceSeq(s, oldChar, newChar)
  ensures forall i :: 0 <= i < |s| ==> v[i] == (if s[i] == oldChar then newChar else s[i])
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant v == ReplaceSeq(s[..i], oldChar, newChar)
    invariant forall j :: 0 <= j < i ==> v[j] == (if s[j] == oldChar then newChar else s[j])
  {
    var v0 := v;

    if s[i] == oldChar {
      v := v + [newChar];
      assert v == v0 + [newChar];
    } else {
      v := v + [s[i]];
      assert v == v0 + [s[i]];
    }

    assert v0 == ReplaceSeq(s[..i], oldChar, newChar);

    // Relate the next prefix to the old prefix by "snoc"
    assert s[..i+1] == s[..i] + [s[i]];

    // Show ReplaceSeq also "snocs" accordingly
    ReplaceSeqSnoc(s[..i], s[i], oldChar, newChar);

    // Conclude the main functional invariant for the next iteration
    assert v == ReplaceSeq(s[..i+1], oldChar, newChar);

    // Conclude the pointwise invariant for the next iteration
    assert forall j :: 0 <= j < i+1 ==> v[j] == (if s[j] == oldChar then newChar else s[j]);
  }
}


// Test cases checked statically
method ReplaceCharsTest(){
  // single occurrence
  var out1 := ReplaceChars("polygon", 'y', 'i');
  assert out1 == "poligon";

  // multiple occurrences
  var out2 := ReplaceChars("polygon", 'o', 'a');
  assert out2 == "palygan";

  // no occurrence
  var out3 := ReplaceChars("polygon", 'a', 'b');
  assert out3 == "polygon";
}
