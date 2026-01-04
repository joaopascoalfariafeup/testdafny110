// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i + 1] // f is in non-descending order
  ensures mult(f) == n // the multiplication of all elements in f equals n
  ensures forall i :: 0 <= i < |f| ==> isPrime(f[i]) // all elements in f are prime
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant div <= n // div is less than or equal to n
      invariant mult(f) * rem == n // the multiplication of all elements in f times rem equals n
      invariant forall i :: 0 <= i < |f| - 1 ==> f[i] <= f[i + 1] // f is in non-descending order
      invariant forall i :: 0 <= i < |f| ==> isPrime(f[i]) // all elements in f are prime
    {
        if rem % div == 0 {
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
}

// ==================== GHOST CODE ====================

ghost function mult(s: seq<nat>): nat
{
  if |s| == 0 then 1 else s[0] * mult(s[1..])
}

ghost function isPrime(n: nat): bool
{
  if n < 2 then false
  else if n == 2 then true
  else forall i :: 2 <= i < n ==> n % i != 0
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert f1 == [2, 2, 3];
}
