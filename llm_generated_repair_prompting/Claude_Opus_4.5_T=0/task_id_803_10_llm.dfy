// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
    ensures result <==> exists k: nat :: k * k == n
{
    var i := 0;
    while i * i < n
        invariant forall k: nat :: k < i ==> k * k < n
    {
        i := i + 1;
    }
    // After loop: i * i >= n
    // Need to show: if i * i != n, then no k exists with k * k == n
    if i * i == n {
        result := true;
    } else {
        // i * i > n
        // For k < i: k * k < n (from invariant)
        // For k >= i: k * k >= i * i > n
        assert forall k: nat :: k >= i ==> k * k >= i * i by {
            forall k: nat | k >= i ensures k * k >= i * i {
                // Since k >= i >= 0, we have k * k >= i * i
                assert k >= i;
                // k * k >= k * i because k >= i >= 0, so k * k = k * k >= k * i
                assert k * k >= k * i;
                // k * i >= i * i because k >= i and i >= 0
                // This needs a helper: (k - i) * i >= 0, so k * i - i * i >= 0
                assert (k - i) * i >= 0;
                assert k * i - i * i >= 0;
                assert k * i >= i * i;
            }
        }
        assert i * i > n;
        assert forall k: nat :: k * k != n by {
            forall k: nat ensures k * k != n {
                if k < i {
                    assert k * k < n;
                } else {
                    assert k * k >= i * i > n;
                }
            }
        }
        result := false;
    }
}


// Test cases checked statically
method IsPerfectSquareTest(){
    var r := IsPerfectSquare(0); 
    assert 0 * 0 == 0;
    assert r;

    r := IsPerfectSquare(1); 
    assert 1 * 1 == 1;
    assert r;
    
    r := IsPerfectSquare(2); assert !r;
    r := IsPerfectSquare(3); assert !r;

    r := IsPerfectSquare(4); 
    assert 2 * 2 == 4;
    assert r;

    r := IsPerfectSquare(1000001); assert !r;
}

