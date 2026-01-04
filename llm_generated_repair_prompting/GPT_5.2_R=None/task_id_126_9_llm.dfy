// Returns the sum of the common divisors of two positive integers.

ghost predicate Divides(d: nat, x: nat)
{
  d > 0 && x % d == 0
}

// Appending a larger element preserves strict increase.
lemma StrictIncreaseAppend(s: seq<nat>, x: nat)
  requires forall i,j :: 0 <= i < j < |s| ==> s[i] < s[j]
  requires forall k :: 0 <= k < |s| ==> s[k] < x
  ensures forall i,j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] < (s + [x])[j]
{
  assert |s + [x]| == |s| + 1;
  forall i,j | 0 <= i < j < |s + [x]|
    ensures (s + [x])[i] < (s + [x])[j]
  {
    if j < |s| {
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == s[j];
      assert s[i] < s[j];
    } else {
      assert j == |s|;
      assert 0 <= i < |s|;
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == x;
      assert s[i] < x;
    }
  }
}

// Ordered list of all common divisors of a and b, from 1 up to min(a,b)
ghost function commonDivisors(a: nat, b: nat): seq<nat>
  requires a > 0 && b > 0
{
  var m := if a <= b then a else b;
  commonDivisorsUpTo(a, b, m)
}

ghost function commonDivisorsUpTo(a: nat, b: nat, n: nat): seq<nat>
  requires a > 0 && b > 0
  requires n <= a + b + 1
  ensures forall d :: d in commonDivisorsUpTo(a,b,n) ==> Divides(d,a) && Divides(d,b)
  ensures forall d :: 1 <= d <= n && Divides(d,a) && Divides(d,b) ==> d in commonDivisorsUpTo(a,b,n)
  ensures forall i,j :: 0 <= i < j < |commonDivisorsUpTo(a,b,n)| ==> commonDivisorsUpTo(a,b,n)[i] < commonDivisorsUpTo(a,b,n)[j]
  ensures forall k :: 0 <= k < |commonDivisorsUpTo(a,b,n)| ==> commonDivisorsUpTo(a,b,n)[k] <= n
  decreases n
{
  if n == 0 then []
  else
    var prev := commonDivisorsUpTo(a, b, n - 1);
    if Divides(n, a) && Divides(n, b) then
      // From the new postcondition on commonDivisorsUpTo(..., n-1):
      assert forall k :: 0 <= k < |prev| ==> prev[k] <= n - 1;
      assert forall k :: 0 <= k < |prev| ==> prev[k] < n;
      StrictIncreaseAppend(prev, n);
      prev + [n]
    else
      prev
}

// Need fuel for unfolding in loop invariants and tests
ghost function {:fuel 10} SumCommonDivisorsUpTo(a: nat, b: nat, n: nat): nat
  requires a > 0 && b > 0
  requires n <= a + b + 1
  decreases n
{
  if n == 0 then 0
  else
    SumCommonDivisorsUpTo(a, b, n - 1) +
    (if Divides(n, a) && Divides(n, b) then n else 0)
}

method SumOfCommonDivisors(a: nat, b: nat) returns (sum: nat)
  requires a > 0 && b > 0
  ensures sum == SumCommonDivisorsUpTo(a, b, if a <= b then a else b)
{
  var m := if a <= b then a else b;

  sum := 0;
  var i: nat := 1;

  while i <= a && i <= b
    invariant 1 <= i
    invariant i <= m + 1
    invariant sum == SumCommonDivisorsUpTo(a, b, i - 1)
    invariant i - 1 <= a + b + 1
    decreases m + 1 - i
  {
    if a % i == 0 && b % i == 0 {
      sum := sum + i;
    }
    assert i <= a + b + 1;
    assert SumCommonDivisorsUpTo(a, b, i)
        == SumCommonDivisorsUpTo(a, b, i - 1) + (if Divides(i, a) && Divides(i, b) then i else 0);

    i := i + 1;
  }

  assert i == m + 1;
  assert sum == SumCommonDivisorsUpTo(a, b, m);
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
