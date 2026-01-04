/* 
* Formal specification and verification of a simple method for calculating 
* Fibonacci numbers applying dynamic programming.
*/

function Fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else Fib(n - 1) + Fib(n - 2)
}

lemma FibSucc(i: nat)
  ensures Fib(i + 2) == Fib(i) + Fib(i + 1)
{
  if i == 0 {
    assert Fib(2) == Fib(1) + Fib(0);
  } else {
    assert Fib(i + 2) == Fib((i + 2) - 1) + Fib((i + 2) - 2);
    assert Fib(i + 2) == Fib(i + 1) + Fib(i);
    assert Fib(i + 2) == Fib(i) + Fib(i + 1);
  }
}


// Iterative computation of the n-th Fibonacci number in time O(n) and space O(1), 
// using dynamic programming 
method CalcFib(n: nat) returns (res: nat) 
  ensures res == Fib(n)
{
    var x, y := 0, 1; // fib(0), fib(1)
    for i := 0 to n 
      invariant x == Fib(i)
      invariant y == Fib(i + 1)
    {
        FibSucc(i);
        x, y := y, x + y; // simultaneous assignment
    }
    return x;
}

// Teste cases checked statically.  
method TestFib()
{
  var f0 := CalcFib(0); assert f0 == 0;
  var f1 := CalcFib(1); assert f1 == 1;
  var f2 := CalcFib(2); assert f2 == 1;
  var f5 := CalcFib(5); assert f5 == 5;
}

