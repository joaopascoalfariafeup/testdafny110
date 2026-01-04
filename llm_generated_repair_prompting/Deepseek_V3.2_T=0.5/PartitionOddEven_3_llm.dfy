// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// That is, there is no even number preceding an odd number. 
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures forall k, l :: 0 <= k < l < a.Length && IsEven(a[k]) ==> IsEven(a[l])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0; // odd numbers are placed to the left of i
    var j := a.Length - 1; // even numbers are placed to the right of j
    while i <= j
      invariant 0 <= i <= j+1 <= a.Length
      invariant forall k :: 0 <= k < i ==> IsOdd(a[k])
      invariant forall k :: j < k < a.Length ==> IsEven(a[k])
      invariant multiset(a[..]) == multiset(old(a[..]))
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
    // Provide helper assertions about the initial array
    assert a[..] == [1, 2, 3];
    PartitionOddEven(a);
    // The postcondition ensures all evens come after all odds
    // So we know the array is partitioned into odds then evens
    // First, prove the partition property for our specific array
    assert forall k, l :: 0 <= k < l < a.Length && IsEven(a[k]) ==> IsEven(a[l]);
    // Now we know the array is partitioned into odds then evens
    // Count the odds in the original array: there are 2 odds (1 and 3)
    // So the first 2 elements must be odd, the last must be even
    assert a[0] % 2 == 1; // first element must be odd
    assert a[1] % 2 == 1; // second element must be odd (since all odds come before evens)
    assert a[2] % 2 == 0; // third element must be even
    // Now check the multiset property to deduce the exact permutation
    assert multiset(a[..]) == multiset([1, 2, 3]);
    // With the above constraints, the only possible permutations are [1,3,2] and [3,1,2]
    // But we need to help Dafny see this by case analysis
    if a[0] == 1 {
        // Then a[1] must be 3 (the only remaining odd)
        assert a[1] == 3;
        assert a[2] == 2;
        assert a[..] == [1, 3, 2];
    } else {
        // Then a[0] must be 3 (the only other odd)
        assert a[0] == 3;
        // a[1] must be 1 (the remaining odd)
        assert a[1] == 1;
        assert a[2] == 2;
        assert a[..] == [3, 1, 2];
    }
    // Final assertion
    assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
}



