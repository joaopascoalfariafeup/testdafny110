// Checks if a natural number is a perfect square.
ghost predicate PerfectSquare(n: nat)
{
  exists k: nat :: k * k == n
}


lemma SquareMonotone(a: nat, b: nat)
  requires a <= b
  ensures a * a <= b * b
{
  var d: nat := b - a;

  calc {
    b * b;
    == { } a * a + 2 * a * d + d * d;
  }
}



lemma PerfectSquareOf(k: nat)
  ensures PerfectSquare(k * k)
{
  assert exists w: nat :: w * w == k * k by { var w := k;
    assert w * w == k * k;
  }
}


method IsPerfectSquare(n: nat) returns(result: bool)
  ensures result <==> PerfectSquare(n)
{
  var i: nat := 0;
  while i * i < n
    invariant forall k: nat :: k < i ==> k * k < n
  {
    i := i + 1;
  }


  if i * i == n {
    return true;
  } else {

    assert forall k: nat :: k * k != n by { forall k: nat ensures k * k != n { if k < i { // use loop invariant
        } else {
          SquareMonotone(i, k);
        }
      }
    }

    return false;
  }
}


// Test cases checked statically
method IsPerfectSquareTest(){
    PerfectSquareOf(0);
    var r := IsPerfectSquare(0); assert r;

    PerfectSquareOf(1);
    r := IsPerfectSquare(1); assert r;
    
    r := IsPerfectSquare(2); assert !r;

    r := IsPerfectSquare(3); assert !r;

    PerfectSquareOf(2);
    r := IsPerfectSquare(4); assert r;

    r := IsPerfectSquare(1000001); assert !r;
}