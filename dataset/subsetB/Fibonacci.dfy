/* 
* Formal specification and verification of a simple method for calculating 
* Fibonacci numbers applying dynamic programming.
*/

// Rcursive definition of the n-th Fibonacci number.
ghost function Fib(n : nat ) : nat {
    if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}  

// Iterative computation of the n-th Fibonacci number in time O(n) and space O(1), 
// using dynamic programming 
method CalcFib(n: nat) returns (res: nat) 
  ensures res == Fib(n)
{
    var x, y := 0, 1; // fib(0), fib(1)
    for i := 0 to n 
      invariant x == Fib(i) && y == Fib(i+1)
    {
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
