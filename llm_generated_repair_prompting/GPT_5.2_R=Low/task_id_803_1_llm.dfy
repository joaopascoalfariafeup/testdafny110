// Checks if a natural number is a perfect square.
predicate PerfectSquare(n: nat)
{
  exists k: nat :: k * k == n
}

lemma SquareMonotone(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
}

lemma SquareEqNonneg(a: int, b: int)
  requires 0 <= a && 0 <= b
  requires a * a == b * b
  ensures a == b
{
  calc {
    a;
    == { assert a * a == b * b; }
    b;
  }
}

method  IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <-> PerfectSquare(n)
{
    var i := 0;
    while i * i < n
      invariant 0 <= i
      invariant i <= n
      invariant forall k: int :: 0 <= k < i ==> k * k < n
      decreases n - i
    {
        i := i + 1;
    }

    if i * i == n {
      assert PerfectSquare(n);
      return true;
    } else {
      assert forall k: nat :: k * k != n;
      return false;
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
