// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
    ensures result <==> exists i: nat :: i * i == n
{
    var i := 0;
    while i * i < n
        invariant 0 <= i * i <= n
        invariant i * i < n ==> !exists j: nat :: j < i && j * j == n
        invariant i <= n // This ensures that i * i will not overflow
        invariant i * i <= n + 1 // Added this invariant to ensure that the loop maintains the invariant 0 <= i * i <= n
        invariant i * i < n || i * i == n // Added this invariant to ensure that the loop maintains the postcondition
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
