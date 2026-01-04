/* 
* Formal specification and verification of a dynamic programming algorithm for calculating
* the binomial coefficient C(n, k).
*/

// Ghost function to compute binomial coefficient (Pascal's triangle definition)
ghost function Comb(n: nat, k: nat): nat
  requires k <= n
{
  if k == 0 then 1
  else if k == n then 1
  else Comb(n-1, k-1) + Comb(n-1, k)
}

// Lemma: C(n, 0) = 1
lemma CombBase(n: nat)
  ensures Comb(n, 0) == 1
{
}

// Lemma: C(n, n) = 1
lemma CombDiag(n: nat)
  ensures Comb(n, n) == 1
{
}

// Lemma to help prove the inner loop invariant on entry
lemma CombDiagShift(i: nat)
  requires i >= 1
  ensures Comb(i - 1, i - 1) == Comb(i, i)
{
  CombDiag(i - 1);
  CombDiag(i);
}

// Iterative calcultion of C(n, k) in time O(k*(n-k)) and space O(n-k), using dynamic programming.
method CalcComb(n: nat, k: nat) returns (res: nat) 
  requires k <= n
  ensures res == Comb(n, k)
{
  var maxj := n - k;
  var c := new nat[maxj + 1]; // contains the values of the ascending diagonal in the Pascal triangle

  // Initialize the left-most ascending diagonal of the Pascal triangle
  forall  j | 0 <= j <= maxj {
       c[j] := 1; // Comb(j, 0)
  }

  // At the begin of each iteration 'i', c[k] contains Comb(k + i - 1, i - 1)
  for i := 1 to k + 1 
    invariant forall j :: 0 <= j <= maxj ==> c[j] == Comb(j + i - 1, i - 1)
  {
    // Prove that c[0] already satisfies the target invariant
    CombDiagShift(i);
    assert c[0] == Comb(i - 1, i - 1) == Comb(i, i);
    
    // Compute the values of the next ascending diagonal in the Pascal triangle
    for j := 1 to maxj + 1
      invariant forall m :: 0 <= m < j ==> c[m] == Comb(m + i, i)
      invariant forall m :: j <= m <= maxj ==> c[m] == Comb(m + i - 1, i - 1)
    {
      // At this point c[j] contains Comb(j+i-1, i-1)  (not updated yet) 
      // and c[j-1] contains Comb(j-1+i, i) (already updated)
      c[j] := c[j] + c[j-1];   
      // At this point c[j] contains Comb(j+i, i)
    } 
  }
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
