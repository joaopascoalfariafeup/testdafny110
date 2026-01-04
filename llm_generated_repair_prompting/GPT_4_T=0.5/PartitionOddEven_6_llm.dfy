
// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// That is, there is no even number preceding an odd number. 
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> (IsEven(a[i]) ==> IsEven(a[j]))
  ensures multiset(a[..]) == old(multiset(a[..])) // postcondition to ensure that the elements in the array 'a' are preserved
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    while i <= j
      invariant 0 <= i <= j+1 <= a.Length
      invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
      invariant forall k :: j < k < a.Length ==> IsEven(a[k])
      invariant multiset(a[..]) == old(multiset(a[..])) // loop invariant to ensure that the elements in the array 'a' are preserved
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
    assert forall i, j :: 0 <= i < j < a.Length ==> (IsEven(a[i]) ==> IsEven(a[j]));
    assert multiset(a[..]) == multiset{1, 2, 3};
}

