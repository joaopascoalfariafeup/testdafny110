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
    var r := IsPerfectSquare(0); assert r;

    r := IsPerfectSquare(1); assert r;
    
    r := IsPerfectSquare(2); assert !r;
    r := IsPerfectSquare(3); assert !r;

    r := IsPerfectSquare(4); assert r;

    r := IsPerfectSquare(1000001); assert !r;
}
