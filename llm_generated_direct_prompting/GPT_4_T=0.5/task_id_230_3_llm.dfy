// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures v.Length == s.Length
  ensures forall i :: 0 <= i < v.Length ==> (if s[i] == ' ' then v[i] == ch else v[i] == s[i])
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v.Length == i
    invariant forall j :: 0 <= j < i ==> (if s[j] == ' ' then v[j] == ch else v[j] == s[j])
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
