lemma SquareMonotoneLt(a: nat, b: nat)
  requires a < b
  ensures a * a < b * b
{
  var d: nat := b - a;
  assert d > 0;
  assert b == a + d;
  calc {
    b * b;
    == (a + d) * (a + d);
    == a * a + 2 * a * d + d * d;
  }
  assert 2 * a * d + d * d > 0;
  assert a * a < b * b;
}

lemma SquareMonotoneLe(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
  if a == b {
  } else {
    SquareMonotoneLt(a, b);
  }
}

// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant i == 0 || (i - 1) * (i - 1) < n
      decreases n - i * i
    {
        i := i + 1;
    }

    assert 0 <= i;
    if i * i == n {
        assert (exists k: nat :: k * k == n) by {
            var k: nat := i;
            assert k * k == n;
        }
    } else {
        assert !(exists k: nat :: k * k == n) by {
            assume exists k: nat :: k * k == n;
            var k: nat :| k * k == n;

            var ii: nat := i;

            assert ii * ii >= n;
            assert ii * ii >= k * k;

            if ii < k {
                SquareMonotoneLt(ii, k);
                assert ii * ii < k * k;
                assert false;
            }
            assert k <= ii;

            if ii == 0 {
                assert n <= ii * ii;
                assert n == 0;
                assert k * k == 0;
                assert k == 0;
                assert i * i == n;
                assert false;
            } else {
                var iim1: nat := ii - 1;
                assert (i - 1) * (i - 1) < n;
                assert iim1 * iim1 < k * k;

                if k <= iim1 {
                    SquareMonotoneLe(k, iim1);
                    assert k * k <= iim1 * iim1;
                    assert false;
                }
                assert k > iim1;
                assert k >= ii;
            }

            assert k == ii;
            assert i * i == n;
            assert false;
        }
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
