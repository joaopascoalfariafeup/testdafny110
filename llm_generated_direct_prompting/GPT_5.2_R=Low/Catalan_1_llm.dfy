/* Catalan numbers are a sequence of natural numbers with significant importance in combinatorial mathematics. 
   They count the number of ways to correctly match parentheses, the number of rooted binary trees with n internal nodes,
   and many other combinatorial structures.
   The n-th Catalan number is given by the formula C(n) = (2n)! / ((n+1)! * n!).
   Catalan numbers can also be defined recursively as C(0) = 1 and C(n) = (4n - 2) * C(n-1) / (n + 1).
*/

function Cat(n: nat): int
  decreases n
{
  if n == 0 then 1
  else (4 * n - 2) * Cat(n - 1) / (n + 1)
}

lemma DivNonneg(a: int, b: int)
  requires a >= 0 && b > 0
  ensures a / b >= 0
{
  assert a / b >= 0;
}

lemma CatNonneg(n: nat)
  ensures Cat(n) >= 0
  decreases n
{
  if n == 0 {
  } else {
    CatNonneg(n - 1);
    assert 4 * n - 2 >= 0;
    assert Cat(n - 1) >= 0;
    assert (4 * n - 2) * Cat(n - 1) >= 0;
    DivNonneg((4 * n - 2) * Cat(n - 1), n + 1);
  }
}


// Iterative calculation using dynamic programming.
method CatalanNumber(n: nat) returns (res: nat)
  ensures res as int == Cat(n)
{
  res := 1; // C(0)
  for i := 1 to n + 1 // upper bound is excluded 
    invariant 1 <= i <= n + 1
    invariant res as int == Cat(i - 1)
  {
    assert Cat(i - 1) >= 0;
    assert (4 * i - 2) >= 0;
    assert (4 * i - 2) * (res as int) >= 0;
    DivNonneg((4 * i - 2) * (res as int), i + 1);

    res := (4 * i - 2) * res / (i + 1);

    assert res as int == Cat(i);
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

