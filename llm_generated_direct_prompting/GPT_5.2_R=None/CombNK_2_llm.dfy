/* 
* Formal specification and verification of a dynamic programming algorithm for calculating
* the binomial coefficient C(n, k).
*/

function Comb(n: nat, k: nat): nat
  requires k <= n
  decreases n, k
{
  if k == 0 || k == n then 1
  else Comb(n - 1, k - 1) + Comb(n - 1, k)
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
    invariant 1 <= i <= k + 1
    invariant forall j :: 0 <= j <= maxj ==> c[j] == Comb(j + i - 1, i - 1)
  {
    // Compute the values of the next ascending diagonal in the Pascal triangle
    for j := 1 to maxj + 1
      invariant 1 <= j <= maxj + 1
      invariant forall t :: 0 <= t < j ==> c[t] == Comb(t + i, i)
      invariant forall t :: j <= t <= maxj ==> c[t] == Comb(t + i - 1, i - 1)
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
