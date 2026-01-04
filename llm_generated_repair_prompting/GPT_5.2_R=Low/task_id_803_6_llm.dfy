// Checks if a natural number is a perfect square.
ghost predicate PerfectSquare(n: nat)
{
  exists k: nat :: k * k == n
}

lemma NatSquarePositive(d: nat)
  requires d > 0
  ensures d * d > 0
{
  // since d > 0, we have d >= 1, hence d*d >= 1
  assert d >= 1;
  calc {
    d * d;
    >= { }
    1 * 1;
    == { }
    1;
  }
}

lemma SquareMonotone(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
  var d: nat := b - a;
  assert b == a + d;

  // b*b = (a+d)^2 = a^2 + 2ad + d^2 >= a^2
  calc {
    b * b;
    == { assert b == a + d; }
    (a + d) * (a + d);
    == { }
    a * a + 2 * a * d + d * d;
    >= { }
    a * a;
  }
}

lemma SquareStrictMonotone(a: nat, b: nat)
  requires a < b
  ensures a * a < b * b
{
  var d: nat := b - a;
  assert d > 0;
  assert b == a + d;

  NatSquarePositive(d);
  // b*b = a^2 + 2ad + d^2, and since d>0, d^2>0, hence b*b > a^2
  calc {
    b * b;
    == { assert b == a + d; }
    (a + d) * (a + d);
    == { }
    a * a + 2 * a * d + d * d;
    >  { }
    a * a;
  }
}

lemma SquareEqNonneg(a: nat, b: nat)
  requires a * a == b * b
  ensures a == b
{
  if a < b {
    SquareStrictMonotone(a, b);
    assert a * a < b * b;
    assert false;
  } else if b < a {
    SquareStrictMonotone(b, a);
    assert b * b < a * a;
    assert false;
  } else {
    // a == b
  }
}

lemma PerfectSquareOf(k: nat)
  ensures PerfectSquare(k * k)
{
  assert exists w: nat :: w * w == k * k by {
    var w := k;
    assert w * w == k * k;
  }
}

lemma NotPerfectSquareBetween(k: nat, n: nat)
  requires k * k < n < (k + 1) * (k + 1)
  ensures !PerfectSquare(n)
{
  if PerfectSquare(n) {
    var t: nat :| t * t == n;

    if t <= k {
      SquareMonotone(t, k);
      assert t * t <= k * k;
      assert t * t < n;
      assert false;
    } else {
      assert k < t;
      assert k + 1 <= t;

      SquareMonotone(k + 1, t);
      assert (k + 1) * (k + 1) <= t * t;
      assert (k + 1) * (k + 1) <= n;
      assert n < (k + 1) * (k + 1);
      assert false;
    }
  }
}

method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> PerfectSquare(n)
{
  var i: nat := 0;
  while i * i < n
    invariant i <= n
    invariant forall k: nat :: k < i ==> k * k < n
    decreases n - i
  {
    i := i + 1;
  }

  // At loop exit: i*i >= n
  assert i * i >= n;

  if i * i == n {
    // witness k = i
    var k: nat := i;
    assert k * k == n;
    assert PerfectSquare(n);
    return true;
  } else {
    // Here: i*i > n
    assert i * i > n;

    // Prove no k has k*k == n
    assert forall k: nat :: k * k != n by
    {
      forall k: nat
        ensures k * k != n
      {
        if k < i {
          // use loop invariant
          assert k * k < n;
          assert k * k != n;
        } else {
          // k >= i ==> k*k >= i*i > n
          assert i <= k;
          SquareMonotone(i, k);
          assert i * i <= k * k;
          assert n < i * i;
          assert n < k * k;
          assert k * k != n;
        }
      }
    }

    return false;
  }
}


// Test cases checked statically
method IsPerfectSquareTest(){
    PerfectSquareOf(0);
    var r := IsPerfectSquare(0); assert r;

    PerfectSquareOf(1);
    r := IsPerfectSquare(1); assert r;
    
    NotPerfectSquareBetween(1, 2);
    r := IsPerfectSquare(2); assert !r;

    NotPerfectSquareBetween(1, 3);
    r := IsPerfectSquare(3); assert !r;

    PerfectSquareOf(2);
    r := IsPerfectSquare(4); assert r;

    // 1000^2 = 1,000,000 < 1,000,001 < 1,002,001 = 1001^2
    NotPerfectSquareBetween(1000, 1000001);
    r := IsPerfectSquare(1000001); assert !r;
}

