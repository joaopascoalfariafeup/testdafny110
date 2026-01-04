// Checks if a natural number is a perfect square.
method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> exists i : nat ::  i * i == n
{
    var i := 0;
    while i * i < n
        invariant forall k :: 0 <= k < i  ==> k * k < n
    {
        i := i + 1;
    }
    SquareMonotonic(i); // helper, call lemma 
    return i * i == n;
}

// Helper lemma to prove monotonicity of squares
lemma SquareMonotonic(i: nat)
    ensures forall j :: j > i ==> j * j > i * i
{
    forall j | j > i
        ensures j * j > i * i
    { } // proved automatically by Dafny
}

// Test cases checked statically
method IsPerfectSquareTest(){
    assert 0 * 0 == 0; // helper
    var r := IsPerfectSquare(0); assert r;

    assert 1 * 1 == 1; // helper
    r := IsPerfectSquare(1); assert r;
    
    r := IsPerfectSquare(2); assert !r;
    r := IsPerfectSquare(3); assert !r;

    assert 2 * 2 == 4; // helper (witness)
    r := IsPerfectSquare(4); assert r;

    r := IsPerfectSquare(1000001); assert !r;
}