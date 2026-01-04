// Difficult example because of the need for auxiliary lemmas.

ghost function {:fuel 0} Pow(x:int, n:nat): int
{
  if n == 0 then 1 else x * Pow(x, n-1)
}

ghost function {:fuel 0} CountInPrefix(a: array<int>, x:int, n:nat): nat
  requires n <= a.Length
  reads a
{
  if n == 0 then 0
  else CountInPrefix(a, x, n-1) + (if a[n-1] == x then 1 else 0)
}

ghost predicate {:fuel 0} AllInPrefix(a: array<int>, s: set<int>, n:nat)
  requires n <= a.Length
  reads a
{
  forall k :: 0 <= k < n ==> a[k] in s
}

ghost predicate {:fuel 0} AllInSetFromPrefix(a: array<int>, s: set<int>, n:nat)
  requires n <= a.Length
  reads a
{
  forall x :: x in s ==> (exists k :: 0 <= k < n && a[k] == x)
}

ghost function {:fuel 0} UniqueProd(a: array<int>, n:nat): int
  requires n <= a.Length
  reads a
{
  if n == 0 then 1
  else
    var x := a[n-1];
    if CountInPrefix(a, x, n-1) == 0 then UniqueProd(a, n-1) * x else UniqueProd(a, n-1)
}

lemma CountInPrefixInc(a: array<int>, x:int, n:nat)
  requires n < a.Length
  ensures CountInPrefix(a, x, n+1) == CountInPrefix(a, x, n) + (if a[n] == x then 1 else 0)
  reads a
{
}

lemma CountInPrefixZeroNotIn(a: array<int>, x:int, n:nat)
  requires n <= a.Length
  ensures CountInPrefix(a, x, n) == 0 <==> (forall k :: 0 <= k < n ==> a[k] != x)
  reads a
{
  if n == 0 {
  } else {
    CountInPrefixZeroNotIn(a, x, n-1);
  }
}

lemma CountInPrefixZeroToPrefix(a: array<int>, x:int, i:nat)
  requires i <= a.Length
  requires CountInPrefix(a, x, i) == 0
  ensures forall k :: 0 <= k < i ==> a[k] != x
  reads a
{
  CountInPrefixZeroNotIn(a, x, i);
}

lemma AllInPrefixAdd(a: array<int>, s:set<int>, i:nat, x:int)
  requires i <= a.Length
  requires AllInPrefix(a, s, i)
  requires x == a[i]
  ensures AllInPrefix(a, s + {x}, i+1)
  reads a
{
  assert forall k :: 0 <= k < i ==> a[k] in s + {x};
  assert a[i] in s + {x};
}

lemma AllInSetFromPrefixAdd(a: array<int>, s:set<int>, i:nat, x:int)
  requires i <= a.Length
  requires AllInSetFromPrefix(a, s, i)
  requires x == a[i]
  ensures AllInSetFromPrefix(a, s + {x}, i+1)
  reads a
{
  assert forall y :: y in s + {x} ==> (exists k :: 0 <= k < i+1 && a[k] == y);
}

lemma UniqueProdStepNew(a: array<int>, i:nat, x:int)
  requires i < a.Length
  requires x == a[i]
  requires CountInPrefix(a, x, i) == 0
  ensures UniqueProd(a, i+1) == UniqueProd(a, i) * x
  reads a
{
  CountInPrefixInc(a, x, i);
  assert CountInPrefix(a, x, i) == 0;
}

lemma UniqueProdStepOld(a: array<int>, i:nat, x:int)
  requires i < a.Length
  requires x == a[i]
  requires CountInPrefix(a, x, i) != 0
  ensures UniqueProd(a, i+1) == UniqueProd(a, i)
  reads a
{
  CountInPrefixInc(a, x, i);
  assert CountInPrefix(a, x, i) != 0;
}

lemma SeenCharact(a: array<int>, seen:set<int>, i:nat, x:int)
  requires i <= a.Length
  requires AllInPrefix(a, seen, i)
  requires AllInSetFromPrefix(a, seen, i)
  ensures (x in seen) <==> (CountInPrefix(a, x, i) != 0)
  reads a
{
  if x in seen {
    var k : int :| 0 <= k < i && a[k] == x;
    assert CountInPrefix(a, x, i) != 0;
  } else {
    assert CountInPrefix(a, x, i) == 0;
  }
}

// Returns the product of the elements of an array 'a', ignoring duplicates.
method UniqueProduct (a: array<int>) returns (product: int)
  ensures product == UniqueProd(a, a.Length)
{
    product := 1;
    var seen : set<int> := {};
    
    for i := 0 to a.Length
      invariant 0 <= i <= a.Length
      invariant product == UniqueProd(a, i)
      invariant AllInPrefix(a, seen, i)
      invariant AllInSetFromPrefix(a, seen, i)
    {
        if a[i] !in seen {
            SeenCharact(a, seen, i, a[i]);
            assert CountInPrefix(a, a[i], i) == 0;
            seen := seen + {a[i]};
            product := product * a[i];
            AllInPrefixAdd(a, seen - {a[i]}, i, a[i]);
            AllInSetFromPrefixAdd(a, seen - {a[i]}, i, a[i]);
            UniqueProdStepNew(a, i, a[i]);
        } else {
            SeenCharact(a, seen, i, a[i]);
            assert CountInPrefix(a, a[i], i) != 0;
            UniqueProdStepOld(a, i, a[i]);
        }
    }
}




// Test cases checked statically by Dafny
// (several auxiliary steps are needed so that the verifier succeeds!)
method UniqueProductTest(){
  var a1 := new int[] [1, 2, 3, 2, 3];
  var out1 := UniqueProduct(a1);
  assert out1 == 6; // the product can be calculated as 1 * 2 * 3 = 6

  var a2 := new int[] [7, 8, 9, 0, 1, 1];
  var out2 := UniqueProduct(a2);
  assert out2 == 0; // so the product can be calculated as 0 * ... = 0
}
