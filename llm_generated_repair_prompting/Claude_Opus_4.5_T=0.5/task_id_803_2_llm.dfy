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

    // At this point: i * i >= n
    // If i * i == n, then n is a perfect square (witnessed by i)
    // If i * i > n, then:
    //   - for all k < i: k * k < n (by invariant)
    //   - for all k >= i: k * k >= i * i > n
    // So no k exists with k * k == n

    if i * i == n {
        return true;
    } else {
        // i * i > n
        // Need to prove: not exists k: nat :: k * k == n
        // For k < i: k * k < n by invariant
        // For k >= i: k * k >= i * i > n
        assert forall k: nat :: k >= i ==> k * k >= i * i;
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

