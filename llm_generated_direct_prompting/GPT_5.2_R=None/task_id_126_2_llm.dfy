ghost function {:fuel 0} SumSeq(s: seq<nat>): nat
{
  if |s| == 0 then 0 else s[|s|-1] + SumSeq(s[..|s|-1])
}

ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  seq i | 1 <= i <= (if a <= b then a else b) && a % i == 0 && b % i == 0 :: i
}

method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= (if a <= b then a else b) + 1
    invariant sum == SumSeq(seq j | 1 <= j < i && a % j == 0 && b % j == 0 :: j)
    decreases (if a <= b then a else b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
      assert SumSeq(seq j | 1 <= j <= i && a % j == 0 && b % j == 0 :: j)
          == SumSeq(seq j | 1 <= j < i && a % j == 0 && b % j == 0 :: j) + i;
    }
    i := i + 1;
  }
  assert i == (if a <= b then a else b) + 1;
  assert commonDivisors(a, b) == (seq j | 1 <= j < i && a % j == 0 && b % j == 0 :: j);
}





// Test cases checked statically
method SumOfCommonDivisorsTest(){
  var out1 := SumOfCommonDivisors(10, 15);
  assert commonDivisors(10, 15) == [1, 5];
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  assert commonDivisors(10, 20) == [1, 2, 5, 10];
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  assert commonDivisors(4, 6) == [1, 2];
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 

}
