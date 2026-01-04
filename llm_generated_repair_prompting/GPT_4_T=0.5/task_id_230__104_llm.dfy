// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
  v := "";
  for i := 0 to |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> (s[j] == ' ' ==> v[j] == ch) && (s[j] != ' ' ==> v[j] == s[j])
  {
    if s[i] == ' ' {
      v := v + ch;
    }
    else {
      v := v + s[i];
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



