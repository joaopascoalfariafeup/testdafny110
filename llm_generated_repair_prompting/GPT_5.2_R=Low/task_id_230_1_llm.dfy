// Replaces all blank characters in a string by a given character.
function ReplaceAllSeq(s: seq<char>, ch: char): seq<char>
{
  if |s| == 0 then []
  else ReplaceAllSeq(s[..|s|-1], ch) + [if s[|s|-1] == ' ' then ch else s[|s|-1]]
}

method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == (if s[i] == ' ' then ch else s[i])
  ensures v == ReplaceAllSeq(s, ch)
{
  v := [];
  for i := 0 to |s|
    invariant |v| == i
    invariant v == ReplaceAllSeq(s[..i], ch)
  {
    if s[i] == ' ' {
      v := v + [ch];
    }
    else {
      v := v + [s[i]];
    }
    assert v == ReplaceAllSeq(s[..i+1], ch);
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
