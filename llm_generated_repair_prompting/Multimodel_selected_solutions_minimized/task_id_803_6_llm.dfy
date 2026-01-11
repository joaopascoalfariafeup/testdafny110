// Checks if a natural number is a perfect square.
ghost predicate PerfectSquare(n: nat)
{
  exists k: nat :: k * k == n
}





lemma PerfectSquareOf(k: nat)
  ensures PerfectSquare(k * k)
{
}

lemma NotPerfectSquareBetween(k: nat, n: nat)
  requires k * k < n < (k + 1) * (k + 1)
{
}

method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> PerfectSquare(n)
{
  var i: nat := 0;
  while i * i < n
    invariant i <= n
    invariant forall k: nat :: k < i ==> k * k < n
  {
    i := i + 1;
  }

  assert i * i >= n;

  if i * i == n {
    var k: nat := i;
    assert k * k == n;
    assert PerfectSquare(n);
    return true;
  } else {
    assert i * i > n;


    return false;
  }
}


// Test cases checked statically
method IsPerfectSquareTest(){
    PerfectSquareOf(0);
    var r := IsPerfectSquare(0); assert r;

    PerfectSquareOf(1);
    r := IsPerfectSquare(1); assert r;
    
    NotPerfectSquareBetween(1, 2);
    r := IsPerfectSquare(2); assert !r;

    r := IsPerfectSquare(3); assert !r;

    r := IsPerfectSquare(4); assert r;

    r := IsPerfectSquare(1000001); assert !r;
}
