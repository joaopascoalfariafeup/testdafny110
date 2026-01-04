// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result == (exists k :: 0 <= k <= n && k * k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i <= n + 1
      invariant forall k :: 0 <= k < i ==> k * k < n
      invariant forall k :: 0 <= k <= n && k * k == n ==> i <= k
    {
        i := i + 1;
    }

    // Additional invariant needed after loop
    assert i * i >= n;
    assert forall k :: 0 <= k < i ==> k * k < n;
    assert forall k :: 0 <= k <= n && k * k == n ==> i <= k;
    // Prove the postcondition
    if i * i == n {
        // Show existence
        assert exists k :: 0 <= k <= n && k * k == n;
    } else {
        // Show non-existence using the invariants
        // Need to prove: forall k :: 0 <= k <= n ==> k * k != n
        // From invariants: forall k :: 0 <= k < i ==> k * k < n
        // and i * i > n (since i * i >= n and i * i != n)
        // Also: forall k :: 0 <= k <= n && k * k == n ==> i <= k
        // But if k >= i, then k * k >= i * i > n, so k * k != n
        // Therefore no k in [0, n] satisfies k * k == n
        assert i * i > n;
        forall k | 0 <= k <= n
          ensures k * k != n
        {
          if k < i {
            assert k * k < n;
          } else {
            assert k >= i;
            assert k * k >= i * i > n;
          }
        }
        assert forall k :: 0 <= k <= n ==> k * k != n;
    }
    return i * i == n;
}


// Test cases checked statically
method IsPerfectSquareTest(){
    var r := IsPerfectSquare(0); 
    assert r;

    r := IsPerfectSquare(1); 
    assert r;
    
    r := IsPerfectSquare(2); 
    assert !r;
    r := IsPerfectSquare(3); 
    assert !r;

    r := IsPerfectSquare(4); 
    assert r;

    r := IsPerfectSquare(1000001); 
    assert !r;
}



