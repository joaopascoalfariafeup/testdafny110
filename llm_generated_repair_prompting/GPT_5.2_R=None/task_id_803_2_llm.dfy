// Checks if a natural number is a perfect square.
method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
  var i := 0;
  while i * i < n
    invariant 0 <= i
    // When i*i < n, we automatically have i*i <= n; this is stable under i := i+1
    invariant i * i < n
    invariant forall k: nat :: 0 <= k < i ==> k * k < n
  {
    i := i + 1;
  }

  // From the loop exit and invariants:
  // - either n == 0 and i == 0, or i*i >= n (exit condition negated)
  // Together with the forall-invariant, this yields the <==> spec.
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
