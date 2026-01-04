// Returns a list with the prime factors of a natural number greater than 1 by non-descending order.
method {:isolate_assertions} PrimeFactors(n: nat) returns (f: seq<nat>)
  requires n > 1
  ensures AllPrime(f)
  ensures IsSorted(f)
  ensures ProdF(f) == n
{
    f  := [];
    var rem := n;
    var div := 2;
    while rem > 1 
      invariant AllPrime(f)
      invariant IsSorted(f)
      invariant ProdB(f) * rem == n
      invariant forall k :: 0 <= k < |f| ==> f[k] <= div
      invariant rem == 1 || div <= rem
      invariant NoFactorBelow(rem, div)
      decreases rem, n - div      
    {
        if rem % div == 0 {
            SmallestDivisorIsPrime(rem, div); // helper, to prove IsPrime(div)           
            NoFactorBelowQuotient(rem, div); // helper, to maintain NoFactorBelow(rem, div) and (rem==1 || div<=rem)         
            DivisionReduces(rem, div);  // helper, to prove decreases         
            f := f + [div]; 
            rem := rem / div;
        }
        else {
            div := div + 1;
        }
    }
    ProdFEqualsProdB(f); // helper
}

// A natural number is prime if it's greater than 1 and has no divisors other than 1 and itself
ghost predicate IsPrime(n: nat)  {
    n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

// All elements in the sequence are prime
ghost predicate AllPrime(f: seq<nat>) {
   forall i :: 0 <= i < |f| ==> IsPrime(f[i])
}

// The sequence is sorted in non-descending order
ghost predicate IsSorted(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// No number from 2 to div-1 divides n
ghost predicate NoFactorBelow(n: nat, div: nat) {
    forall k :: 2 <= k < div ==> n % k != 0
}

// Product of all elements in the sequence (from the back)
ghost function ProdB(s: seq<nat>): nat {
    if |s| == 0 then 1 else s[|s|-1] * ProdB(s[..|s|-1])
}

// Alternative product from the front (easier for induction proofs)
ghost function ProdF(s: seq<nat>): nat {
    if |s| == 0 then 1 else s[0] * ProdF(s[1..])
}

// Lemma: ProdF equals Prod (proved by induction)
lemma {:isolate_assertions} ProdFEqualsProdB(s: seq<nat>)
  ensures ProdF(s) == ProdB(s)
{
    if |s| > 1 {
      var s1 := s[1..];
      calc {
        ProdF(s);
        s[0] * ProdF(s1);
        {ProdFEqualsProdB(s1);}
        s[0] * ProdB(s1);
        s[0] * (s1[|s1|-1] * ProdB(s1[..|s1|-1]));
        (s[0] * ProdB(s1[..|s1|-1])) * s1[|s1|-1];
        {assert s1[..|s1|-1] == s[1..|s|-1];}
        (s[0] * ProdB(s[1..|s|-1])) * s[|s|-1];
        {ProdFEqualsProdB(s[1..|s|-1]);}
        (s[0] * ProdF(s[1..|s|-1])) * s[|s|-1];
        ProdF(s[..|s|-1]) * s[|s|-1];
        {ProdFEqualsProdB(s[..|s|-1]);}
        ProdB(s[..|s|-1]) * s[|s|-1];
        ProdB(s);
      }
    }
}

// Lemma: if d divides n and no number below d divides n, then d is prime.
lemma SmallestDivisorIsPrime(n: nat, d: nat)
  requires n > 0
  requires d > 1
  requires n % d == 0
  requires NoFactorBelow(n, d)
  ensures IsPrime(d)
{
  if  k :| 2 <= k < d && d % k == 0 {
      DivisorTransitive(n, d, k);
      assert n % k == 0; // contradicts NoFactorBelow(n, d), so d is prime
  }
}

// Lemma: if NoFactorBelow(n, d) and d divides n, then NoFactorBelow(n/d, d) and n/d is not a factor of n below d
lemma NoFactorBelowQuotient(n: nat, d: nat)
  requires n > 0
  requires d > 1
  requires n % d == 0
  requires NoFactorBelow(n, d)
  ensures NoFactorBelow(n / d, d)
  ensures ! (1 < n / d < d)
{
  var q := n / d;
  DivModUnique(n, q, d, 0); //  ==> n % q == 0, so q=1 or q >= d 
  if k :| 2 <= k < d && q % k == 0 {
    DivisorTransitive(n, q, k);
    assert n % k == 0; // contradicts NoFactorBelow(n, d), so NoFactorBelow(n/d, d) holds
  } 
}

// Lemma: if b divides a and c divides b, then c divides a
lemma DivisorTransitive(a: nat, b: nat, c: nat)
  requires b >= 1 && c >= 1
  requires a % b == 0
  requires b % c == 0
  ensures a % c == 0
{
    DivModUnique(a, c, (a / b) * (b / c), 0);
}

// Proof by contradition of Euclidean division uniqueness
lemma DivModUnique(a: nat, b: nat, q: nat, r: nat)
  requires a == q * b + r
  requires 0 <= r < b
  ensures a / b == q
  ensures a % b == r
{
    var q' := a / b;
    var r' := a % b;
    if q > q' {
        assert q' * b <= (q - 1) * b == q * b - b;
        assert r' >= b;   // contradicts r' < b
    } else if q < q'{
        assert q' * b >= (q + 1) * b == q * b + b;
        assert r >= b;  // contradicts r < b
    }
}

// Lemma: dividing n by d with d > 1 and n > 0 reduces n 
lemma DivisionReduces(n: nat, d: nat)
  requires n > 0
  requires d > 1
  requires n % d == 0
  ensures n / d < n
{
    assert n == (n / d) * d > (n / d);
}

// ==================== helpers: UNIQUENESS PROOF BY INDUCTION ====================

// Main uniqueness lemma - proved by induction on n
lemma {:isolate_assertions} PrimeFactorizationUnique(f1: seq<nat>, f2: seq<nat>, n: nat)
  requires n > 1
  requires AllPrime(f1) && IsSorted(f1) && ProdF(f1) == n
  requires AllPrime(f2) && IsSorted(f2) && ProdF(f2) == n
  ensures f1 == f2
{    
    var p1, tail1 := f1[0], f1[1..];
    var p2, tail2 := f2[0], f2[1..];      
    DivModUnique(n, p1,  ProdF(tail1), 0); // head divides product
    DivModUnique(n, p2,  ProdF(tail2), 0); // idem
    AllFactorsIncluded(f1, n); // product contains all prime factors
    AllFactorsIncluded(f2, n); // idem  
    assert p1 == p2; // so f1 and f2 have the same head    
    var m := n / p1; // proceed to the rest  
    if m > 1 {
      DivisionReduces(n, p1); // to guarante decreses      
      PrimeFactorizationUnique(tail1, tail2, m); // inductive proof
    }
}

// Helper: all prime dividors of a product of primes, must be factors of the product
lemma AllFactorsIncluded(s: seq<nat>, n: nat)
  requires |s| > 0
  requires AllPrime(s)
  requires ProdF(s) == n
  ensures forall p :: IsPrime(p) && n % p == 0 ==> p in s 
{
    forall p | IsPrime(p) && n % p == 0
      ensures p in s
    {
        PrimeDivisorMustAppear(s, p);
    }
}

// ==================== helpers: EUCLID's LEMMA  ====================

// This is Euclid's lemma: if a prime p divides a product of primes, p must be one of them
lemma PrimeDivisorMustAppear(s: seq<nat>, p: nat)
  requires AllPrime(s)
  requires IsPrime(p) && ProdF(s) % p == 0
  ensures p in s
{
  if |s| > 0 {
    var head, tail := s[0], s[1..];
    EuclidCoreLemma(p, head, ProdF(tail)); // p divides head or tailProd
    if head % p == 0 {
      // since head is prime, p = head, so p is in 's'
    } else {
      // p divides tailProd, so, by induction, p is in tail, so p is in 's'
      PrimeDivisorMustAppear(tail, p);
    }
  }
}

// Euclid's core lemma: if prime p divides a*b, then p divides a or p divides b.
// Proved by contradiction using the property that gcd(p,a) = 1 when p is prime and p doesn't divide a.
lemma EuclidCoreLemma(p: nat, a: nat, b: nat)
  requires IsPrime(p)
  requires (a * b) % p == 0
  ensures a % p == 0 || b % p == 0
{
  if a % p != 0 && b % p != 0 {
    var g := Gcd(p, a);
    // Gcd divides p, and p is prime, so Gcd = 1 or p
    // But if Gcd = p then it divides a, contradicting the precondition; so must be 1
    assert g == 1;
    // By Bezout's identity, there exist integers x, y such that px + ay = 1
    var (x, y) := BezoutCoefficients(p, a);
    // Multiplying by b: bpx + bay = b <==> p(bx + (ab/p)y) = b, so p divides b  
    DivModUnique(b, p, b * x + ((a * b) / p) * y, 0); 
    assert b % p == 0; // contradiction    
  }
}

// GCD function using Euclidean algorithm, and some of its properties
ghost function Gcd(a: nat, b: nat): nat
  requires a > 0 || b > 0
  ensures Gcd(a, b) > 0
  ensures a % Gcd(a, b) == 0
  ensures b % Gcd(a, b) == 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a > b then 
    var g := Gcd(a - b, b);
    DivModUnique(a, g, (a - b) / g + b / g, 0);
    g
  else 
    var g := Gcd(a, b - a);
    DivModUnique(b, g, a / g + (b - a) / g, 0);
    g
}

// Get Bezout coefficients
ghost function BezoutCoefficients(a: nat, b: nat): (r: (int, int))
  requires a > 0 && b > 0
  ensures a * r.0 + b * r.1 == Gcd(a, b)
  decreases a + b
{
  if a == b then (1, 0)
  else if a > b then
    var r' := BezoutCoefficients(a - b, b);
    (r'.0, r'.1 - r'.0)
  else
    var r' := BezoutCoefficients(a, b - a);
    (r'.0 - r'.1, r'.1)
}

// ==================== TEST CODE ====================

method TestPrimeFactors() {
    var f1 := PrimeFactors(12);    
    assert [2, 2, 3][..2] == [2, 2]; // helper
    assert [2, 2][..1] == [2]; // helper    
    PrimeFactorizationUnique(f1, [2, 2, 3], 12); // helper    
    assert f1 == [2, 2, 3];
}