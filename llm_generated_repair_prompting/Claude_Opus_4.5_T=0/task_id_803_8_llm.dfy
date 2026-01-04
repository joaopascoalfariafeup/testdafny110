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
                // k * k >= k * i because k >= i (multiply both sides by k)
                // k * i >= i * i because k >= i (multiply both sides by i)
                calc >= {
                    k * k;
                    { assert k >= i; }
                    i * k;
                    { assert k >= i; }
                    i * i;
                }
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

