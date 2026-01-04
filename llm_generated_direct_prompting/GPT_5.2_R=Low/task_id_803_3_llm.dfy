lemma MulNonNeg(x: int, y: int)
  requires 0 <= x && 0 <= y
  ensures 0 <= x * y
{
}

lemma SquareMonotone(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
  assert b * b - a * a == (b - a) * (b + a);
  assert 0 <= b - a;
  assert 0 <= b + a;
  MulNonNeg(b - a, b + a);
  assert 0 <= (b - a) * (b + a);
  assert a * a <= b * b;
}

// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant forall k: int :: 0 <= k < i ==> k * k < n
      decreases n - i * i
    {
        i := i + 1;
    }

    assert 0 <= i;
    assert i * i >= n;

    if i * i == n {
      assert exists k: nat :: k * k == n by {
        exists i as k;
      }
    } else {
      assert i * i > n;

      assert forall k: nat :: k * k != n by {
        intro k;
        if (k as int) < i {
          assert 0 <= (k as int) < i;
          assert (k as int) * (k as int) < n;
        } else {
          assert i <= (k as int);
          SquareMonotone(i, k as int);
          assert i * i <= (k as int) * (k as int);
          assert n < (k as int) * (k as int);
        }
      };
    }

    return i * i == n;
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
