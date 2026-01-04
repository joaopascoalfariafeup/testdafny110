/* Catalan numbers are a sequence of natural numbers with significant importance in combinatorial mathematics. 
   They count the number of ways to correctly match parentheses, the number of rooted binary trees with n internal nodes,
   and many other combinatorial structures.
   The n-th Catalan number is given by the formula C(n) = (2n)! / ((n+1)! * n!).
   Catalan numbers can also be defined recursively as C(0) = 1 and C(n) = (4n - 2) * C(n-1) / (n + 1).
*/


ghost function Fact(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Fact(n - 1)
}

ghost function CatalanClosed(n: nat): nat
{
  Fact(2 * n) / (Fact(n + 1) * Fact(n))
}

lemma FactPos(n: nat)
  ensures Fact(n) > 0
{
}

lemma CatalanRecurrenceStep(i: nat)
  requires i >= 1
  ensures CatalanClosed(i) == ((4 * i - 2) * CatalanClosed(i - 1)) / (i + 1)
{
  FactPos(i - 1);
  FactPos(i);
  FactPos(i + 1);
  FactPos(2 * i - 1);
  FactPos(2 * i);

  assert Fact(2 * i) == (2 * i) * Fact(2 * i - 1);
  assert Fact(2 * i - 1) == (2 * i - 1) * Fact(2 * i - 2);
  assert Fact(i + 1) == (i + 1) * Fact(i);
  assert Fact(i) == i * Fact(i - 1);

  calc {
    ((4 * i - 2) * CatalanClosed(i - 1)) / (i + 1);
    == { }
    ((4 * i - 2) * (Fact(2 * (i - 1)) / (Fact((i - 1) + 1) * Fact(i - 1)))) / (i + 1);
    == { assert 2 * (i - 1) == 2 * i - 2; }
    ((4 * i - 2) * (Fact(2 * i - 2) / (Fact(i) * Fact(i - 1)))) / (i + 1);
    == { assert 4 * i - 2 == 2 * (2 * i - 1); }
    ((2 * (2 * i - 1)) * (Fact(2 * i - 2) / (Fact(i) * Fact(i - 1)))) / (i + 1);
    == { }
    ((2 * i * (2 * i - 1)) * Fact(2 * i - 2)) / ((i + 1) * Fact(i) * Fact(i - 1));
    == { assert Fact(2 * i) == (2 * i) * (2 * i - 1) * Fact(2 * i - 2); }
    Fact(2 * i) / ((i + 1) * Fact(i) * Fact(i - 1));
    == { assert Fact(i + 1) == (i + 1) * Fact(i); assert Fact(i) == i * Fact(i - 1); }
    Fact(2 * i) / (Fact(i + 1) * Fact(i));
    == { }
    CatalanClosed(i);
  }
}

// Iterative calculation using dynamic programming.
method CatalanNumber(n: nat) returns (res: nat)
  ensures res == CatalanClosed(n)
{
  res := 1; // C(0)
  for i := 1 to n + 1 // upper bound is excluded 
    invariant 1 <= i <= n + 1
    invariant res == CatalanClosed(i - 1)
  {
    CatalanRecurrenceStep(i);
    res := (4 * i - 2) * res / (i + 1);      
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

