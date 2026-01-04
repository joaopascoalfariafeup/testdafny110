/* Catalan numbers are a sequence of natural numbers with significant importance in combinatorial mathematics. 
   They count the number of ways to correctly match parentheses, the number of rooted binary trees with n internal nodes,
   and many other combinatorial structures.
   The n-th Catalan number is given by the formula C(n) = (2n)! / ((n+1)! * n!).
   Catalan numbers can also be defined recursively as C(0) = 1 and C(n) = (4n - 2) * C(n-1) / (n + 1).
*/

function {:opaque :fuel 50} CatalanInt(n: nat): int
{
  if n == 0 then 1
  else (4 * n - 2) * CatalanInt(n - 1) / (n + 1)
}

lemma {:opaque} CatalanIntNonNeg(n: nat)
  ensures 0 <= CatalanInt(n)
{
  reveal CatalanInt;
  if n == 0 {
  } else {
    CatalanIntNonNeg(n - 1);
    assert 0 <= CatalanInt(n - 1);
    assert 0 < 4 * n - 2;
    assert 0 < n + 1;
    assert 0 <= (4 * n - 2) * CatalanInt(n - 1);
    assert 0 <= (4 * n - 2) * CatalanInt(n - 1) / (n + 1);
  }
}

lemma {:opaque} CatalanIntStep(k: nat)
  requires k > 0
  ensures CatalanInt(k) == (4 * k - 2) * CatalanInt(k - 1) / (k + 1)
{
  reveal CatalanInt;
}

lemma {:opaque} CatalanIntIterStep(i: int, r: nat)
  requires 1 <= i
  requires r as int == CatalanInt((i - 1) as nat)
  ensures (4 * i - 2) * (r as int) / (i + 1) == CatalanInt(i as nat)
{
  var k := i as nat;
  assert k > 0;
  CatalanIntStep(k);

  assert 4 * k - 2 == 4 * i - 2;
  assert k + 1 == i + 1;
  assert k - 1 == (i - 1) as nat;

  assert (4 * i - 2) * (r as int) / (i + 1) ==
         (4 * i - 2) * CatalanInt((i - 1) as nat) / (i + 1);
  assert (4 * i - 2) * CatalanInt((i - 1) as nat) / (i + 1) ==
         (4 * k - 2) * CatalanInt(k - 1) / (k + 1);
}

// Iterative calculation using dynamic programming.
method CatalanNumber(n: nat) returns (res: nat)
  ensures res as int == CatalanInt(n)
{
  res := 1; // C(0)
  for i := 1 to n + 1 // upper bound is excluded 
    invariant 1 <= i <= n + 1
    invariant 0 <= res
    invariant res as int == CatalanInt((i - 1) as nat)
  {
    CatalanIntNonNeg((i - 1) as nat);
    assert 0 <= res;

    // help the verifier relate the iterative update to the recursive definition
    assert (4 * i - 2) * (res as int) / (i + 1) == CatalanInt(i as nat) by {
      CatalanIntIterStep(i, res);
    }

    res := (4 * i - 2) * res / (i + 1);

    assert res as int == CatalanInt(i as nat);
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
