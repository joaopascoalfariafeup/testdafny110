lemma SquareMonotoneInt(a:int, b:int)
  requires 0 <= a <= b
  ensures a*a <= b*b
{
  calc {
    b*b - a*a;
    == (b - a) * (b + a);
  }
  assert 0 <= b - a;
  assert 0 <= b + a;
  assert 0 <= (b - a) * (b + a);
}

lemma SquareMonotoneNat(a:nat, b:nat)
  requires a <= b
  ensures a*a <= b*b
{
  SquareMonotoneInt(a as int, b as int);
}

// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result == (exists k:nat :: k*k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant forall j:int :: 0 <= j < i ==> j*j < n
      decreases (n as int) - i*i
    {
        i := i + 1;
    }
    assert i*i >= n;
    if i*i == n {
      assert (i as nat) * (i as nat) == n;
      assert (exists k:nat :: k*k == n);
    } else {
      assert i*i > n;
      assert !(exists k:nat :: k*k == n) by {
        assume exists k:nat :: k*k == n;
        var k: nat :| k*k == n;
        if (k as int) < i {
          assert (k as int)*(k as int) < n;
          assert (k as int)*(k as int) == n;
          assert false;
        } else {
          assert i <= k as int;
          SquareMonotoneInt(i, k as int);
          assert i*i <= (k as int)*(k as int);
          assert (k as int)*(k as int) == n;
          assert i*i <= n;
          assert false;
        }
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
