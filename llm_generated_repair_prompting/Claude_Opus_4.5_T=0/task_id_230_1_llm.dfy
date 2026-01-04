// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall k :: 0 <= k < |s| ==> (s[k] == ' ' ==> v[k] == ch)
  ensures forall k :: 0 <= k < |s| ==> (s[k] != ' ' ==> v[k] == s[k])
{
  v := [];
  for i := 0 to |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> v[k] == ch)
    invariant forall k :: 0 <= k < i ==> (s[k] != ' ' ==> v[k] == s[k])
  {
    if s[i] == ' ' {
      v := v + [ch];
    }
    else {
      v := v + [s[i]];
    }
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
