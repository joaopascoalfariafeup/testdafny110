// Replaces all blank characters in a string by a given character.

function ReplaceSeq(s: seq<char>, ch: char): seq<char>
{
  if |s| == 0 then []
  else ReplaceSeq(s[..|s|-1], ch) + [if s[|s|-1] == ' ' then ch else s[|s|-1]]
}

lemma ReplaceSeqExtend(s: seq<char>, ch: char, i: int)
  requires 0 <= i < |s|
  ensures ReplaceSeq(s[..i+1], ch) == ReplaceSeq(s[..i], ch) + [if s[i] == ' ' then ch else s[i]]
{
  assert |s[..i+1]| == i + 1;
  assert (s[..i+1])[..|s[..i+1]|-1] == (s[..i+1])[..i];
  assert (s[..i+1])[..i] == s[..i];
  assert (s[..i+1])[|s[..i+1]|-1] == (s[..i+1])[i];
  assert (s[..i+1])[i] == s[i];
}

method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures v == ReplaceSeq(s, ch)
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == ReplaceSeq(s[..i], ch)
  {
    if s[i] == ' ' {
      v := v + [ch];
    }
    else {
      v := v + [s[i]];
    }
    ReplaceSeqExtend(s, ch, i);
    assert v == ReplaceSeq(s[..i+1], ch);
  }
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
