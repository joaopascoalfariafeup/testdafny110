// Checks if a natural number is a perfect square.
method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
  var i := 0;
  while i * i < n
    invariant 0 <= i
    // Strong enough to prove the postcondition on exit:
    //  - i is the least nat such that i*i >= n
    invariant forall k: nat :: k < i ==> k * k < n
    decreases n - i  // since i*i < n implies i < n for nat n>0
  {
    i := i + 1;
  }

  // At loop exit: i*i >= n and forall k<i: k*k < n, hence:
  //   i*i==n  <==>  exists k: k*k==n
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
