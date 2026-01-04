// Function to count the number of blanks in a string
ghost function CountBlanks(s: string): nat
{
  if |s| == 0 then 0
  else (if s[|s|-1] == ' ' then 1 else 0) + CountBlanks(s[..|s|-1])
}

// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall k :: 0 <= k < |s| ==> (s[k] != ' ' ==> v[k] == s[k]) && (s[k] == ' ' ==> v[k] == ch)
  ensures CountBlanks(v) == 0
{
  v := [];
  for i := 0 to |s|
    invariant |v| == i
    invariant forall k :: 0 <= k < i ==> (s[k] != ' ' ==> v[k] == s[k]) && (s[k] == ' ' ==> v[k] == ch)
    invariant CountBlanks(v) == i - CountBlanks(s[..i])
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
