// Replaces all blank characters in a string by a given character.
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures IsMapSeq(s, v, c => if c == ' ' then ch else c)
{
  v := [];
  for i := 0 to |s|
    invariant IsMapSeq(s[..i], v, c => if c == ' ' then ch else c)
  {
    if s[i] == ' ' {
      v := v + [ch];
    }
    else {
      v := v + [s[i]];
    }
  }
}

// Checks if a sequence 't' is the result of applying a function 'f'
// to every element of a sequence 's'.
ghost predicate IsMapSeq<T, E>(s: seq<T>, t: seq<E>, f: T -> E) {
  |t| == |s| && forall i :: 0 <= i < |s| ==> t[i] == f(s[i])
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