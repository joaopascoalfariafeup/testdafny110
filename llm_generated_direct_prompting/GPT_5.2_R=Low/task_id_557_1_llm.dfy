// Returns a new string with the case of each character in the input string toggled.
method ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures v == TogglePrefix(s, |s|)
{
  v := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant v == TogglePrefix(s, i)
  {
    TogglePrefixStep(s, i);
    v := v + [Toggle(s[i])];
  }
}

// Auxiliary function to toggle the case of a character.
function Toggle(c: char): char {
  if 'a' <= c <= 'z' then c - ('a' - 'A') 
  else if 'A' <= c <= 'Z' then c + ('a' - 'A')
  else c
}

function TogglePrefix(s: string, n: nat): string
  requires n <= |s|
{
  if n == 0 then ""
  else TogglePrefix(s, n - 1) + [Toggle(s[n - 1])]
}

lemma TogglePrefixStep(s: string, i: nat)
  requires i < |s|
  ensures TogglePrefix(s, i + 1) == TogglePrefix(s, i) + [Toggle(s[i])]
{
}

// Test cases checked statically.
method ToggleCaseTest(){
  var out1 := ToggleCase("Python");
  assert out1=="pYTHON";

  var out2 := ToggleCase("LIttLE");
  assert out2=="liTTle";
}
