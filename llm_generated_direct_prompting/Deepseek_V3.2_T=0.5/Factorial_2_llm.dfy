
// Computes the factorial of a number 'n' in time O(n) and space O(1).
method CalcFact(n: nat) returns (f: nat) 
  ensures f == Factorial(n)
{
  f := 1;
  for i := 1 to n + 1 
    invariant f == Factorial(i-1)
  {
    f := f * i;
  }
  return f;
}

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

// Test cases checked statically.    
method TestFact() 
{
  var f0 := CalcFact(0); assert f0 == 1;
  var f1 := CalcFact(1); assert f1 == 1;
  var f2 := CalcFact(2); assert f2 == 2;
  var f3 := CalcFact(3); assert f3 == 6;
 }

