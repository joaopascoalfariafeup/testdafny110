// Replaces all blank characters in a string by a given character.
function ReplaceAllSeq(s: seq<char>, ch: char): seq<char>
{
  if |s| == 0 then []
  else ReplaceAllSeq(s[..|s|-1], ch) + [if s[|s|-1] == ' ' then ch else s[|s|-1]]
}

lemma ReplaceAllSeqExtend(s: seq<char>, ch: char, i: int)
  requires 0 <= i < |s|
  ensures ReplaceAllSeq(s[..i+1], ch) ==
            ReplaceAllSeq(s[..i], ch) + [if s[i] == ' ' then ch else s[i]]
{
  // Unfold ReplaceAllSeq on the prefix s[..i+1]
  assert |s[..i+1]| == i + 1;
  assert (s[..i+1])[..|(s[..i+1])|-1] == s[..i];
  assert (s[..i+1])[|(s[..i+1])|-1] == s[i];

  calc {
    ReplaceAllSeq(s[..i+1], ch);
    == { }
    ReplaceAllSeq((s[..i+1])[..|(s[..i+1])|-1], ch)
      + [if (s[..i+1])[|(s[..i+1])|-1] == ' ' then ch else (s[..i+1])[|(s[..i+1])|-1]];
    == { }
    ReplaceAllSeq(s[..i], ch) + [if s[i] == ' ' then ch else s[i]];
  }
}

lemma ReplaceAllSeqSpec(s: seq<char>, ch: char)
  ensures |ReplaceAllSeq(s, ch)| == |s|
  ensures forall i :: 0 <= i < |s| ==> ReplaceAllSeq(s, ch)[i] == (if s[i] == ' ' then ch else s[i])
{
  if |s| == 0 {
  } else {
    ReplaceAllSeqSpec(s[..|s|-1], ch);

    // Helpful unfolding
    assert ReplaceAllSeq(s, ch) ==
      ReplaceAllSeq(s[..|s|-1], ch) + [if s[|s|-1] == ' ' then ch else s[|s|-1]];

    // Length
    assert |ReplaceAllSeq(s, ch)| == |ReplaceAllSeq(s[..|s|-1], ch)| + 1;
    assert |ReplaceAllSeq(s[..|s|-1], ch)| == |s| - 1;

    // Pointwise
    assert forall i :: 0 <= i < |s| ==>
      ReplaceAllSeq(s, ch)[i] == (if s[i] == ' ' then ch else s[i]) by
    {
      forall i | 0 <= i < |s|
        ensures ReplaceAllSeq(s, ch)[i] == (if s[i] == ' ' then ch else s[i])
      {
        if i < |s| - 1 {
          // Index is in the recursive prefix
          assert ReplaceAllSeq(s, ch)[i] == ReplaceAllSeq(s[..|s|-1], ch)[i];
          // Use IH on the prefix
          assert ReplaceAllSeq(s[..|s|-1], ch)[i] == (if s[i] == ' ' then ch else s[i]);
        } else {
          // Index is the last position
          assert i == |s| - 1;
          assert ReplaceAllSeq(s, ch)[i] == (if s[|s|-1] == ' ' then ch else s[|s|-1]);
        }
      }
    }
  }
}

method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == (if s[i] == ' ' then ch else s[i])
  ensures v == ReplaceAllSeq(s, ch)
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant v == ReplaceAllSeq(s[..i], ch)
  {
    if s[i] == ' ' {
      v := v + [ch];
      assert v == ReplaceAllSeq(s[..i], ch) + [ch];
    }
    else {
      v := v + [s[i]];
      assert v == ReplaceAllSeq(s[..i], ch) + [s[i]];
    }

    ReplaceAllSeqExtend(s, ch, i);
    assert v == ReplaceAllSeq(s[..i+1], ch);
  }

  // Convert invariant at i==|s| into the desired postconditions
  assert s[..|s|] == s;
  assert v == ReplaceAllSeq(s, ch);

  ReplaceAllSeqSpec(s, ch);
  assert |v| == |s|;
  assert forall i :: 0 <= i < |s| ==> v[i] == (if s[i] == ' ' then ch else s[i]);
}


// Test cases checked statically.
method ReplaceBlanksWithCharTest(){
  var res1 := ReplaceBlanksWithChar("hello people",'@');
  assert res1 == "hello@people";
  
  var res2 := ReplaceBlanksWithChar("python program language",'$');
  assert res2 == "python$program$language";
  
  var res3 := ReplaceBlanksWithChar("blank space",'-');
  assert res3=="blank-space";
}

