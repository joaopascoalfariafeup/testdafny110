// Auxiliary predicate to check if a character represents a digit
predicate IsDigit(c: char) {
  '0' <= c <= '9'
}

// Checks if a string represents an unsigned integer, that is, a sequence
// of one or more decimal digits.
method IsInteger(s: string) returns (result: bool)
  ensures result == (|s| > 0 && (forall i :: 0 <= i < |s| ==> IsDigit(s[i])))
{
  if |s| == 0 {
    result := false;
    return;
  } 
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (forall j :: 0 <= j < i ==> IsDigit(s[j]))
  {
    if !IsDigit(s[i]) {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}

method IsIntegerTest(){
  var s1 := "python";
  var res1 := IsInteger(s1);
  // Add helper assertion to verify the test
  assert |s1| == 6;
  assert s1[0] == 'p' && !IsDigit(s1[0]);
  assert !res1;

  var res2 := IsInteger("1");
  assert res2;

  var res3 := IsInteger("12345");
  assert res3;

  var res4 := IsInteger("");
  assert !res4;
}

