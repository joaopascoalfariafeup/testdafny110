// Checks if a natural number is a perfect square.
method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> (exists k: nat :: k * k == n)
{
  var i := 0;
  while i * i < n
    invariant 0 <= i
    // i is the least nat such that i*i >= n
    invariant forall k: nat :: k < i ==> k * k < n
    decreases n - i
  {
    i := i + 1;
  }

  return i * i == n;
}


// Test cases checked statically
method IsPerfectSquareTest(){
  var r := IsPerfectSquare(0);
  assert (exists k: nat :: k * k == 0); // witness k=0
  assert r;

  r := IsPerfectSquare(1);
  assert (exists k: nat :: k * k == 1); // witness k=1
  assert r;
  
  r := IsPerfectSquare(2); assert !r;
  r := IsPerfectSquare(3); assert !r;

  r := IsPerfectSquare(4);
  assert (exists k: nat :: k * k == 4); // witness k=2
  assert r;

  r := IsPerfectSquare(1000001); assert !r;
}
