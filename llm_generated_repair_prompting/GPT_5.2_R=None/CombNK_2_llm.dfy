/* 
* Formal specification and verification of a dynamic programming algorithm for calculating
* the binomial coefficient C(n, k).
*/

ghost function {:fuel 5} Binom(n: nat, k: nat): nat
  requires k <= n
  decreases n, k
{
  if k == 0 || k == n then 1
  else Binom(n - 1, k - 1) + Binom(n - 1, k)
}

// Iterative calcultion of C(n, k) in time O(k*(n-k)) and space O(n-k), using dynamic programming.
method CalcComb(n: nat, k: nat) returns (res: nat) 
  requires k <= n
  ensures res == Binom(n, k)
{
  var maxj := n - k;
  var c := new nat[maxj + 1]; // contains the values of the ascending diagonal in the Pascal triangle

  // Initialize the left-most ascending diagonal of the Pascal triangle
  for j := 0 to maxj + 1
    invariant 0 <= j <= maxj + 1
    invariant forall t :: 0 <= t < j ==> c[t] == 1
  {
    c[j] := 1; // Comb(j, 0)
  }
  assert forall j :: 0 <= j <= maxj ==> c[j] == 1;

  // At the begin of each iteration 'i', c[k] contains Comb(k + i - 1, i - 1)
  for i := 1 to k + 1 
    invariant 1 <= i <= k + 1
    invariant forall j :: 0 <= j <= maxj ==> c[j] == Binom(j + i - 1, i - 1)
  {
    // Compute the values of the next ascending diagonal in the Pascal triangle
    for j := 1 to maxj + 1
      invariant 1 <= j <= maxj + 1
      invariant forall t :: 0 <= t < j ==> c[t] == Binom(t + i, i)
      invariant forall t :: j <= t <= maxj ==> c[t] == Binom(t + i - 1, i - 1)
    {
      // At this point c[j] contains Comb(j+i-1, i-1)  (not updated yet) 
      // and c[j-1] contains Comb(j-1+i, i) (already updated)
      assert c[j] == Binom(j + i - 1, i - 1);
      assert c[j-1] == Binom((j-1) + i, i);

      // Use the recursive definition of Binom at (n=j+i, k=i)
      assert Binom(j + i, i) == Binom(j + i - 1, i - 1) + Binom(j + i - 1, i);

      c[j] := c[j] + c[j-1];   
      // At this point c[j] contains Comb(j+i, i)
      assert c[j] == Binom(j + i, i);
    } 
  }
  assert c[maxj] == Binom(maxj + k, k);
  return c[maxj];
}


// Test cases checked statically and dynamically  
method Main() 
{
  // Checked statically
  var c1 := CalcComb(5, 0); assert c1 == 1;
  var c2 := CalcComb(5, 2); assert c2 == 10;
  var c3 := CalcComb(5, 5); assert c3 == 1;

  // Checked dynamically
  var c4 := CalcComb(40, 10);
  expect c4 == 847660528;
}
