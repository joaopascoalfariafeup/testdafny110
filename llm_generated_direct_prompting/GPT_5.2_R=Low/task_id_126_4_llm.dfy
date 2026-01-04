function Min(a: nat, b: nat): nat {
  if a <= b then a else b
}

function {:fuel 50} CommonDivsUpTo(a: nat, b: nat, m: nat): seq<nat>
  requires a > 0 && b > 0
  decreases m
{
  if m == 0 then []
  else
    var s := CommonDivsUpTo(a, b, m - 1);
    if a % m == 0 && b % m == 0 then s + [m] else s
}

function {:fuel 50} commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  CommonDivsUpTo(a, b, Min(a, b))
}

function {:fuel 50} SumSeq(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

function {:fuel 50} SumCommonUpTo(a: nat, b: nat, k: nat): nat
  requires a > 0 && b > 0
  decreases k
{
  if k == 0 then 0
  else SumCommonUpTo(a, b, k - 1) + (if a % k == 0 && b % k == 0 then k else 0)
}

lemma {:fuel 50} SumSeq_CommonDivsUpTo(a: nat, b: nat, m: nat)
  requires a > 0 && b > 0
  ensures SumSeq(CommonDivsUpTo(a, b, m)) == SumCommonUpTo(a, b, m)
  decreases m
{
  if m == 0 {
  } else {
    SumSeq_CommonDivsUpTo(a, b, m - 1);
    if a % m == 0 && b % m == 0 {
      assert CommonDivsUpTo(a, b, m) == CommonDivsUpTo(a, b, m - 1) + [m];
      assert SumSeq(CommonDivsUpTo(a, b, m)) ==
        SumSeq(CommonDivsUpTo(a, b, m - 1) + [m]);
      assert SumSeq(CommonDivsUpTo(a, b, m - 1) + [m]) ==
        SumSeq(CommonDivsUpTo(a, b, m - 1)) + m;
    } else {
      assert CommonDivsUpTo(a, b, m) == CommonDivsUpTo(a, b, m - 1);
    }
  }
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonUpTo(a, b, Min(a, b))
  ensures sum == SumSeq(commonDivisors(a, b))
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= Min(a, b) + 1
    invariant sum == SumCommonUpTo(a, b, i - 1)
    decreases Min(a, b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
  SumSeq_CommonDivsUpTo(a, b, Min(a, b));
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
