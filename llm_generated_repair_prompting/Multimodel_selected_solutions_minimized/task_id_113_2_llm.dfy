// Auxiliary predicate to check if a character represents a digit
predicate IsDigit(c: char) {
  '0' <= c <= '9'
}

predicate AllDigits(s: string) {
  forall i :: 0 <= i < |s| ==> IsDigit(s[i])
}

// Checks if a string represents an unsigned integer, that is, a sequence
// of one or more decimal digits.
method IsInteger(s: string) returns (result: bool)
  ensures result <==> (|s| > 0 && AllDigits(s))
{
  if |s| == 0 {
    return false;
  } 
  for i := 0 to |s|
    invariant AllDigits(s[..i])
  {
    if !IsDigit(s[i]) {
      return false;
    }
  }
  return true;
}

method IsIntegerTest(){
  var s1 := "python";
  assert !IsDigit(s1[0]);
  var res1 := IsInteger(s1);
  assert !res1;

  var res2 := IsInteger("1");
  assert res2;

  var res3 := IsInteger("12345");
  assert res3;

  var res4 := IsInteger("");
  assert !res4;
}