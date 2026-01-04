// Checks if a natural number is a perfect square.
lemma SquareMonotone(a: nat, b: nat)
  ensures a <= b ==> a * a <= b * b
{
}

method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i <= n + 1
      invariant forall k: nat :: 0 <= k < i ==> k * k < n
      decreases n + 1 - i
    {
        i := i + 1;
    }
    result := i * i == n;

    if result {
        assert (exists k: nat :: k * k == n);
    } else {
        assert i * i > n;
        assert forall k: nat :: k * k != n
        {
            forall k: nat
              ensures k * k != n
            {
                if k < i {
                    assert k * k < n;
                } else {
                    SquareMonotone(i, k);
                    assert i * i <= k * k;
                    assert k * k > n;
                }
            }
        };
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
