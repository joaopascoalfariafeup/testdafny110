// Checks if a natural number is a perfect square.
predicate PerfectSquare(n: nat)
{
  exists k: nat :: k * k == n
}

lemma SquareMonotone(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
  // a*a <= a*b <= b*b
  have h1: a * a <= a * b by
  {
    // multiply a <= b by nonnegative a
    assert a <= b;
    assert 0 <= a;
  }
  have h2: a * b <= b * b by
  {
    // multiply a <= b by nonnegative b
    assert a <= b;
    assert 0 <= b;
  }
  calc {
    a * a;
    <= { }
    a * b;
    <= { }
    b * b;
  }
}

lemma SquareStrictMonotone(a: int, b: int)
  requires 0 <= a < b
  ensures a * a < b * b
{
  // b >= a+1 ==> b*b >= (a+1)^2 = a^2 + 2a + 1 > a^2
  assert b >= a + 1;
  calc {
    b * b;
    >= { }
    (a + 1) * (a + 1);
    == { }
    a * a + 2 * a + 1;
    >  { assert 0 <= a; }
    a * a;
  }
}

lemma SquareEqNonneg(a: int, b: int)
  requires 0 <= a && 0 <= b
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
  var i := 0;
  while i * i < n
    invariant 0 <= i
    invariant i <= n
    invariant forall k: int :: 0 <= k < i ==> k * k < n
    decreases n - i
  {
    i := i + 1;
  }

  // At loop exit: i*i >= n
  assert i * i >= n;

  if i * i == n {
    // witness k = i
    assert 0 <= i;
    var k: nat := i as nat;
    assert k * k == n;
    assert PerfectSquare(n);
    return true;
  } else {
    // Here: i*i > n
    assert i * i > n;

    // Prove no k has k*k == n
    assert forall k: nat :: k * k != n by
    {
      intro k: nat;
      if k < i {
        // use loop invariant (k is int here)
        assert (k as int) * (k as int) < n;
        assert k * k != n;
      } else {
        // k >= i ==> k*k >= i*i > n
        SquareMonotone(i, k as int);
        assert (k as int) * (k as int) >= i * i;
        assert k * k > n;
        assert k * k != n;
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
