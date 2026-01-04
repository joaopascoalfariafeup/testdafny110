// Returns a new string with the case of each character in the input string toggled.
method ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> v[i] == Toggle(s[i])
{
  v := [];
  for i := 0 to |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> v[j] == Toggle(s[j])
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


// Test cases checked statically.
method ToggleCaseTest(){
  var out1 := ToggleCase("Python");
  assert out1=="pYTHON";

  var out2 := ToggleCase("LIttLE");
  assert out2=="liTTle";
}
