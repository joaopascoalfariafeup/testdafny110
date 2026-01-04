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
    assert forall k: nat :: k >= i ==> k * k >= i * i;
    return i * i == n;
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
