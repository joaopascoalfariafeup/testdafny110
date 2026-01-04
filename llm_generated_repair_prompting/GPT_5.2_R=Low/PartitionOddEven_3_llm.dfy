// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// That is, there is no even number preceding an odd number. 
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == old(multiset(a[..]))
  ensures forall p, q :: 0 <= p < q < a.Length ==> !(IsEven(a[p]) && IsOdd(a[q]))
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    while i <= j
      invariant 0 <= i <= a.Length
      invariant -1 <= j < a.Length
      invariant i <= j + 1
      invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
      invariant forall k :: j < k < a.Length ==> IsEven(a[k])
      invariant multiset(a[..]) == old(multiset(a[..]))
      decreases j - i + 1
     {
        assert 0 <= i < a.Length;
        assert 0 <= j < a.Length;

        if IsEven(a[i]) && IsOdd(a[j]) { a[i], a[j] := a[j], a[i]; } // swap
        if IsOdd(a[i]) { i := i + 1; }
        if IsEven(a[j]) { j := j - 1; }
    }
}
 
predicate IsOdd(n: nat) { 
  n % 2 == 1 
}

predicate IsEven(n: nat) { 
  n % 2 == 0 
}

lemma NatOddOrEven(n: nat)
  ensures IsOdd(n) || IsEven(n)
{
  if n % 2 == 0 {
  } else {
    assert n % 2 == 1;
  }
}

lemma NatNotOddAndEven(n: nat)
  ensures !(IsOdd(n) && IsEven(n))
{
  if IsOdd(n) {
    assert n % 2 == 1;
    assert n % 2 != 0;
  }
}

// Useful fact about singleton multisets
lemma SingletonCount<T>(y: T, x: T)
  ensures multiset([y])[x] == (if x == y then 1 else 0)
{
  if x == y {
  } else {
  }
}

lemma InIffCountPos<T>(s: seq<T>, x: T)
  ensures (x in s) <==> multiset(s)[x] > 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var t := s[..|s|-1];
    var y := s[|s|-1];
    InIffCountPos(t, x);

    // Help Dafny relate multiset counts after appending y
    assert s == t + [y];
    assert multiset(s) == multiset(t + [y]);
    assert multiset(t + [y]) == multiset(t) + multiset([y]);
    SingletonCount(y, x);
    assert multiset(s)[x] == multiset(t)[x] + multiset([y])[x];

    if x == y {
      assert multiset([y])[x] == 1;
      assert multiset(s)[x] == multiset(t)[x] + 1;
    } else {
      assert multiset([y])[x] == 0;
      assert multiset(s)[x] == multiset(t)[x];
    }
  }
}

lemma TwoElemsAre13Or31(s: seq<nat>)
  requires |s| == 2
  requires multiset(s) == multiset([1, 3])
  ensures s == [1, 3] || s == [3, 1]
{
  // show s[0] is in [1,3]
  assert multiset(s)[s[0]] > 0;
  assert multiset([1,3])[s[0]] > 0;
  InIffCountPos([1,3], s[0]);
  assert s[0] in [1,3];
  assert s[0] == 1 || s[0] == 3;

  if s[0] == 1 {
    // then s[1] must be 3 (otherwise counts don't match)
    assert multiset(s)[1] == multiset([1,3])[1];
    assert multiset(s)[1] == 1;
    if s[1] != 3 {
      assert s[1] == 1 || s[1] == 3; // since s[1] in [1,3]
      if s[1] == 1 {
        assert multiset(s)[1] >= 2; // contradiction with count 1
      }
    }
    assert s[1] == 3;
  } else {
    // s[0]==3, similarly s[1]==1
    assert s[1] == 1 || s[1] == 3;
    assert multiset(s)[3] == multiset([1,3])[3];
    assert multiset(s)[3] == 1;
    if s[1] != 1 {
      if s[1] == 3 {
        assert multiset(s)[3] >= 2; // contradiction with count 1
      }
    }
    assert s[1] == 1;
  }
}

lemma ResultForInput123(a: array<nat>)
  requires a.Length == 3
  requires multiset(a[..]) == multiset([1,2,3])
  requires forall p, q :: 0 <= p < q < a.Length ==> !(IsEven(a[p]) && IsOdd(a[q]))
  ensures a[..] == [1,3,2] || a[..] == [3,1,2]
{
  // a[2] must be even; otherwise earlier positions cannot be even, contradicting presence of 2
  if IsOdd(a[2]) {
    assert 0 <= 0 < 2 < a.Length;
    assert 0 <= 1 < 2 < a.Length;
    assert !(IsEven(a[0]) && IsOdd(a[2]));
    assert !(IsEven(a[1]) && IsOdd(a[2]));
    assert !IsEven(a[0]);
    assert !IsEven(a[1]);
    NatOddOrEven(a[0]); NatNotOddAndEven(a[0]);
    NatOddOrEven(a[1]); NatNotOddAndEven(a[1]);
    assert IsOdd(a[0]);
    assert IsOdd(a[1]);

    // but 2 must be in the array, contradiction
    assert multiset(a[..])[2] == multiset([1,2,3])[2];
    assert multiset([1,2,3])[2] == 1;
    assert multiset(a[..])[2] > 0;
    InIffCountPos(a[..], 2);
    assert 2 in a[..];
  }
  assert IsEven(a[2]);

  // a[2] is one of {1,2,3}
  assert multiset(a[..])[a[2]] > 0;
  assert multiset([1,2,3])[a[2]] > 0;
  InIffCountPos([1,2,3], a[2]);
  assert a[2] in [1,2,3];
  assert a[2] == 1 || a[2] == 2 || a[2] == 3;

  // only 2 is even among {1,2,3}
  assert IsOdd(1); assert IsOdd(3);
  if a[2] == 1 {
    assert IsOdd(a[2]);
    assert false;
  }
  if a[2] == 3 {
    assert IsOdd(a[2]);
    assert false;
  }
  assert a[2] == 2;

  // Reduce to first two elements being {1,3}
  assert a[..] == a[..2] + [a[2]];
  assert multiset(a[..]) == multiset(a[..2]) + multiset([a[2]]);
  assert multiset([1,2,3]) == multiset([1,3]) + multiset([2]);
  assert multiset(a[..2]) == multiset([1,3]);

  TwoElemsAre13Or31(a[..2]);
  if a[..2] == [1,3] {
    assert a[..] == [1,3] + [2];
    assert a[..] == [1,3,2];
  } else {
    assert a[..2] == [3,1];
    assert a[..] == [3,1] + [2];
    assert a[..] == [3,1,2];
  }
}

method testPartitionOddEven() {
    var a: array<nat> := new [] [1, 2, 3];
    // Capture initial contents so we can use PartitionOddEven's multiset preservation
    var s0 := a[..];
    assert s0 == [1,2,3];

    PartitionOddEven(a);

    // Help the verifier connect the postconditions to the concrete expected results
    assert a.Length == 3;
    assert multiset(a[..]) == multiset(s0);
    assert multiset(a[..]) == multiset([1,2,3]);

    ResultForInput123(a);
    assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}

