// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// That is, there is no even number preceding an odd number. 
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> exists m :: 0 <= m < a.Length && a[k] == old(a[m])
  ensures forall k :: 0 <= k < a.Length ==> exists m :: 0 <= m < a.Length && old(a[k]) == a[m]
  ensures forall p, q :: 0 <= p < q < a.Length ==> !(IsEven(a[p]) && IsOdd(a[q]))
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    ghost var s := multiset(a[..]);
    while i <= j
      invariant 0 <= i <= a.Length
      invariant -1 <= j < a.Length
      invariant i <= j + 1
      invariant multiset(a[..]) == s
      invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
      invariant forall k :: j < k < a.Length ==> IsEven(a[k])
     {
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

method testPartitionOddEven() {
    var a: array<nat> := new [] [1, 2, 3];
    PartitionOddEven(a);
    assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}

