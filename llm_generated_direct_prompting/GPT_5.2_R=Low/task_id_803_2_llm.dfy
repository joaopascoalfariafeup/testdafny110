// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant forall k:int :: 0 <= k < i ==> k * k < n
      decreases n - i * i
    {
        i := i + 1;
    }

    assert 0 <= i;
    assert i * i >= n;

    if i * i == n {
        assert exists k: nat :: k * k == n by {
            assert 0 <= i;
            assert (i as nat) * (i as nat) == n;
        }
    } else {
        assert !(exists k: nat :: k * k == n) by {
            if exists k: nat :: k * k == n {
                var k: nat :| k * k == n;
                if (k as int) < i {
                    assert (k as int) * (k as int) < n;
                    assert k * k < n;
                    assert false;
                } else if (k as int) > i {
                    assert i + 1 <= k as int;
                    assert i * i < (i + 1) * (i + 1);
                    assert (i + 1) * (i + 1) <= (k as int) * (k as int);
                    assert i * i < (k as int) * (k as int);
                    assert i * i < n;
                    assert false;
                } else {
                    assert (k as int) == i;
                    assert k == i as nat;
                    assert i * i == n;
                    assert false;
                }
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
