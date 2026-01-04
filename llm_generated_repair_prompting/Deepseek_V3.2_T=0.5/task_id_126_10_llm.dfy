// Returns the sum of the common divisors of two positive integers.
method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsSeq(a, b)
{
  sum := 0; // sum of the common divisors so far
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && i <= b + 1
    invariant sum == SumCommonDivisorsSeqUpTo(a, b, i - 1)
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    i := i + 1;
  }
}

function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
  ensures forall k :: 0 <= k < |result| ==> result[k] > 0 && a % result[k] == 0 && b % result[k] == 0
  ensures forall d: nat :: 1 <= d <= a && d <= b && a % d == 0 && b % d == 0 ==> d in result
{
  if a == 0 || b == 0 then []
  else var s := commonDivisors(a, b - 1);
       if b <= a && a % b == 0 && b % b == 0 then s + [b]
       else s
} by method {
  var res: seq<nat> := [];
  var i: nat := 1;
  while i <= a && i <= b
    invariant 1 <= i <= a + 1 && i <= b + 1
    invariant forall k :: 0 <= k < |res| ==> res[k] > 0 && a % res[k] == 0 && b % res[k] == 0
    invariant forall d: nat :: 1 <= d < i && d <= a && d <= b && a % d == 0 && b % d == 0 ==> d in res
  {
    if a % i == 0 && b % i == 0 {
      res := res + [i];
    }
    i := i + 1;
  }
  return res;
}

ghost function SumCommonDivisorsSeq(a: nat, b: nat): nat
  requires a > 0 && b > 0
  ensures result == SumCommonDivisorsSeqUpTo(a, b, if a <= b then a else b)
{
  SumCommonDivisorsSeqUpTo(a, b, if a <= b then a else b)
}

ghost function SumCommonDivisorsSeqUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a && n <= b
  ensures result == sumCommonDivisorsUpTo(a, b, n)
{
  if n == 0 then 0
  else if a % n == 0 && b % n == 0 then SumCommonDivisorsSeqUpTo(a, b, n - 1) + n
       else SumCommonDivisorsSeqUpTo(a, b, n - 1)
}

ghost function sumCommonDivisorsUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a && n <= b
{
  var total: nat := 0;
  var i: nat := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant total == sumCommonDivisorsUpToLoop(a, b, i - 1)
  {
    if a % i == 0 && b % i == 0 {
      total := total + i;
    }
    i := i + 1;
  }
  total
}

ghost function sumCommonDivisorsUpToLoop(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a && n <= b
{
  if n == 0 then 0
  else if a % n == 0 && b % n == 0 then sumCommonDivisorsUpToLoop(a, b, n - 1) + n
       else sumCommonDivisorsUpToLoop(a, b, n - 1)
}

// Test cases checked statically
method SumOfCommonDivisorsTest(){
  var out1 := SumOfCommonDivisors(10, 15);
  // Provide helper assertions to help Dafny verify the test assertions
  assert commonDivisors(10, 15) == [1, 5] by {
    // Explicitly compute common divisors to help verification
    var cd := commonDivisors(10, 15);
    assert |cd| == 2;
    assert cd[0] == 1 && cd[1] == 5;
  }
  assert out1 == 6;
  
  var out2 := SumOfCommonDivisors(10, 20);
  assert commonDivisors(10, 20) == [1, 2, 5, 10] by {
    var cd := commonDivisors(10, 20);
    assert |cd| == 4;
    assert cd[0] == 1 && cd[1] == 2 && cd[2] == 5 && cd[3] == 10;
  }
  assert out2 == 18;
  
  var out3 := SumOfCommonDivisors(4,6);
  assert commonDivisors(4, 6) == [1, 2] by {
    var cd := commonDivisors(4, 6);
    assert |cd| == 2;
    assert cd[0] == 1 && cd[1] == 2;
  }
  assert out3 == 3;

  // @invalid: var out4 := SumOfCommonDivisors(0, 1); 
  // @invalid: var out5 := SumOfCommonDivisors(1, 0); 
  // @invalid: var out6 := SumOfCommonDivisors(0, 0); 

}

