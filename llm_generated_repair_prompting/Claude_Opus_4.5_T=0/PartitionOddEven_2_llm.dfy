// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// That is, there is no even number preceding an odd number. 
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] in old(a[..])
  ensures forall k :: 0 <= k < a.Length ==> old(a[k]) in a[..]
  ensures forall k, l :: 0 <= k < l < a.Length ==> !(IsEven(a[k]) && IsOdd(a[l]))
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    while i <= j
      invariant 0 <= i <= a.Length
      invariant -1 <= j < a.Length
      invariant i <= j + 1
      invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
      invariant forall k :: j < k < a.Length ==> IsEven(a[k])
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall k :: 0 <= k < a.Length ==> a[k] in multiset(old(a[..]))
     {
        if IsEven(a[i]) && IsOdd(a[j]) { a[i], a[j] := a[j], a[i]; } // swap
        if IsOdd(a[i]) { i := i + 1; }
        if IsEven(a[j]) { j := j - 1; }
    }
    assert forall k :: 0 <= k < a.Length ==> a[k] in multiset(a[..]);
    assert forall k :: 0 <= k < a.Length ==> a[k] in multiset(old(a[..]));
}
 
predicate IsOdd(n: nat) { 
  n % 2 == 1 
}

predicate IsEven(n: nat) { 
  n % 2 == 0 
}

lemma MultisetContainment(a: seq<nat>, b: seq<nat>)
  requires multiset(a) == multiset(b)
  ensures forall k :: 0 <= k < |a| ==> a[k] in b
  ensures forall k :: 0 <= k < |b| ==> b[k] in a
{
  forall k | 0 <= k < |a|
    ensures a[k] in b
  {
    assert a[k] in multiset(a);
    assert a[k] in multiset(b);
  }
  forall k | 0 <= k < |b|
    ensures b[k] in a
  {
    assert b[k] in multiset(b);
    assert b[k] in multiset(a);
  }
}

method testPartitionOddEven() {
    var a: array<nat> := new [] [1, 2, 3];
    var old_a := a[..];
    assert old_a == [1, 2, 3];
    PartitionOddEven(a);
    assert multiset(a[..]) == multiset([1, 2, 3]);
    assert IsOdd(a[0]);
    assert IsOdd(a[1]) || IsEven(a[1]);
    assert IsEven(a[2]);
    // a[2] must be 2 (the only even number)
    assert a[2] == 2;
    // a[0] and a[1] must be 1 and 3 in some order
    assert a[0] in [1, 3] && a[1] in [1, 3];
    assert a[0] != a[1];
    assert (a[0] == 1 && a[1] == 3) || (a[0] == 3 && a[1] == 1);
    assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}
