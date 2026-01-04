/* Catalan numbers are a sequence of natural numbers with significant importance in combinatorial mathematics. 
   They count the number of ways to correctly match parentheses, the number of rooted binary trees with n internal nodes,
   and many other combinatorial structures.
   The n-th Catalan number is given by the formula C(n) = (2n)! / ((n+1)! * n!).
   Catalan numbers can also be defined recursively as C(0) = 1 and C(n) = (4n - 2) * C(n-1) / (n + 1).
*/

function {:fuel 20} Cat(n: nat): nat
  decreases n
{
  if n == 0 then 1 else ((4 * n - 2) * Cat(n - 1)) / (n + 1)
}


// Iterative calculation using dynamic programming.
method CatalanNumber(n: nat) returns (res: nat)
  ensures res == Cat(n)
{
  res := 1; // C(0)
  for i := 1 to n + 1 // upper bound is excluded 
    invariant 1 <= i <= n + 1
    invariant res == Cat(i - 1)
  {
    res := (4 * i - 2) * res / (i + 1);      
    assert res == Cat(i);
  }
  return res;
}

// Test cases checked statically.
method testCalcC() {
    var c0 := CatalanNumber(0); assert c0 == 1;
    var c1 := CatalanNumber(1); assert c1 == 1;
    var c2 := CatalanNumber(2); assert c2 == 2;
    var c3 := CatalanNumber(3); assert c3 == 5;
    var c4 := CatalanNumber(4); assert c4 == 14;
    var c5 := CatalanNumber(5); assert c5 == 42;
}

