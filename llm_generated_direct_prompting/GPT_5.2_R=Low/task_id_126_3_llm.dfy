function Min(a: nat, b: nat): nat {
  if a <= b then a else b
}

function {:fuel 200} SumCommonDivisorsUpTo(k: nat, a: nat, b: nat): nat
  requires a > 0 && b > 0
{
  if k == 0 then 0
  else SumCommonDivisorsUpTo(k - 1, a, b) + (if a % k == 0 && b % k == 0 then k else 0)
}

function {:fuel 200} commonDivisorsUpTo(k: nat, a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  if k == 0 then []
  else
    var prev := commonDivisorsUpTo(k - 1, a, b);
    if a % k == 0 && b % k == 0 then prev + [k] else prev
}

function {:fuel 200} commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  commonDivisorsUpTo(Min(a, b), a, b)
}

// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsUpTo(Min(a, b), a, b)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= Min(a, b) + 1
    invariant sum == SumCommonDivisorsUpTo(i - 1, a, b)
    decreases Min(a, b) + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    assert sum == SumCommonDivisorsUpTo(i, a, b);
    i := i + 1;
  }
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
