// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures |f| > 0
  ensures forall i :: 0 <= i < |f| ==> f[i] > 1
  ensures forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i+1]
  ensures product(f) == n
  ensures forall i :: 0 <= i < |f| ==> isPrime(f[i])
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant 1 <= rem <= n
      invariant div >= 2
      invariant product(f) * rem == n
      invariant forall i :: 0 <= i < |f| ==> f[i] >= 2
      invariant forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i+1]
      invariant forall i :: 0 <= i < |f| ==> isPrime(f[i])
      invariant forall p :: 2 <= p < div && isPrime(p) ==> rem % p != 0
      invariant forall i :: 0 <= i < |f| ==> f[i] <= div
      invariant forall p :: 2 <= p < div && isPrime(p) ==> (forall i :: 0 <= i < |f| ==> f[i] != p) || (rem % p == 0 && p == div)
    {
        if rem % div == 0 {
            f := f + [div]; 
            rem := rem / div;
            // Maintain ordering invariant after appending
            assert |f| > 0;
            if |f| > 1 {
                assert f[|f|-2] <= f[|f|-1] by {
                    // The last element is 'div', and previous elements are <= current div
                    // because we never decrease div and only append when divisible
                    // Also from invariant: forall i :: 0 <= i < |f|-1 ==> f[i] <= f[i+1]
                    // The new element is appended at the end, so we need to show
                    // that the second-to-last element (if exists) is <= div
                    // This follows from the new invariant forall i :: 0 <= i < |f| ==> f[i] <= div
                    // and the fact that before appending, |f| was |f|-1, so for i = |f|-2,
                    // we had f[i] <= div (since div hasn't changed in this branch)
                }
            }
        }
        else {
            div := div + 1;
        }
    }
}

function product(s: seq<nat>): nat {
  if |s| == 0 then 1 else s[|s|-1] * product(s[..|s|-1])
}

predicate isPrime(p: nat) {
  p > 1 && forall d :: 2 <= d < p ==> p % d != 0
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    // Add helper assertions to prove the test outcome
    assert product([2,2,3]) == 12;
    assert product(f1) == 12;
    assert |f1| == 3;
    assert f1[0] == 2;
    assert f1[1] == 2;
    assert f1[2] == 3;
    assert f1 == [2, 2, 3];
}







