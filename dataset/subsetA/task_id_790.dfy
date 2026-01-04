// Checks if all elements at even indices are even.
method IsEvenAtIndexEven(s: seq<int>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |s| && IsEven(i) ==> IsEven(s[i])
{
  for i := 0 to |s|
    invariant forall k :: 0 <= k < i && IsEven(k) ==> IsEven(s[k])
  {
    if IsEven(i) && !IsEven(s[i]) {
      return false;
    }
  }
  return true;
}

// Checks if a number is even.
predicate IsEven(n: int) {
  n % 2 == 0
}

// Tests.
method IsEvenAtIndexEvenTest(){
  var s1: seq<int> := [3, 2, 1];
  var res1 := IsEvenAtIndexEven(s1);
  assert !IsEven(s1[0]); // proof heper (counter-example)
  assert !res1;

  var s2: seq<int> := [1, 2, 3];
  var res2 := IsEvenAtIndexEven(s2);
  assert !IsEven(s2[0]); // proof heper (counter-example)
  assert !res2;

  var s3: seq<int> := [2, 1, 4];
  var res3 := IsEvenAtIndexEven(s3);
  assert res3;
}