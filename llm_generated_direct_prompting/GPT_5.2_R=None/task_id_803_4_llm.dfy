// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant i * i <= n
      decreases n - i * i
    {
        i := i + 1;
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
