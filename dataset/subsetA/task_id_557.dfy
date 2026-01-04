// Returns a new string with the case of each character in the input string toggled.
method ToggleCase(s: string) returns (v: string)
  ensures IsMapSeq(s, v, Toggle) 
{
  v := [];
  for i := 0 to |s|
    invariant IsMapSeq(s[..i], v, Toggle)
  {
    v := v + [Toggle(s[i])];
  }
}

// Auxiliary function to toggle the case of a character.
function Toggle(c: char): char {
  if 'a' <= c <= 'z' then c - ('a' - 'A') 
  else if 'A' <= c <= 'Z' then c + ('a' - 'A')
  else c
}

// Checks if a sequence 't' is the result of applying a function 'f'
// to every element of a sequence 's'.
ghost predicate IsMapSeq<T, E>(s: seq<T>, t: seq<E>, f: T -> E) {
  |t| == |s| && forall i :: 0 <= i < |s| ==> t[i] == f(s[i])
}

// Test cases checked statically.
method ToggleCaseTest(){
  var out1 := ToggleCase("Python");
  assert out1=="pYTHON";

  var out2 := ToggleCase("LIttLE");
  assert out2=="liTTle";
}