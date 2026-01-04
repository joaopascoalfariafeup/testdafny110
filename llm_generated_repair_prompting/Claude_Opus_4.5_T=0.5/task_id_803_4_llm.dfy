// Helper lemma: squaring is monotonic for naturals
lemma SquareMonotonic(a: nat, b: nat)
    requires a <= b
    ensures a * a <= b * b
{
    // a <= b implies a * a <= a * b (multiply by a)
    assert a * a <= a * b;
    // a <= b implies a * b <= b * b (multiply by b)
    assert a * b <= b * b;
    // transitivity: a * a <= b * b
}

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
        assert i * i == n;
        return true;
    } else {
        // i * i > n
        // Need to prove: not exists k: nat :: k * k == n
        // For k < i: k * k < n by invariant
        // For k >= i: k * k >= i * i > n
        forall k: nat 
            ensures k >= i ==> k * k >= i * i
        {
            if k >= i {
                SquareMonotonic(i, k);
            }
        }
        assert forall k: nat :: k >= i ==> k * k >= i * i;
        assert i * i > n;
        assert forall k: nat :: k >= i ==> k * k > n;
        // Combined with invariant: forall k < i: k * k < n
        // So for all k: k * k != n
        assert forall k: nat :: k * k != n;
        return false;
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



