// Finds the index of the first odd number in an arrray.
// If there is no odd number, returns -1.
method FindFirstOdd(a: array<int>) returns (index: int)
  ensures 0 <= index < a.Length ==> IsOdd(a[index]) && (forall k :: 0 <= k < index ==> !IsOdd(a[k]))
  ensures index == -1 ==> (forall k :: 0 <= k < a.Length ==> !IsOdd(a[k]))
{
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> !IsOdd(a[k])
    {
        if IsOdd(a[i]) {
            index := i;
            return;
        }
        i := i + 1;
    }
    index := -1;
}


predicate IsOdd(x: int) {
    x % 2 != 0
}

// Test cases checked statically.
method FindFirstOddTest(){
    // first
    var a1 := new int[] [1, 3, 5];
    // Helper assertions to establish array contents
    assert a1[0] == 1 && a1[1] == 3 && a1[2] == 5;
    // Additional helper to prove IsOdd for array elements
    assert IsOdd(a1[0]);
    assert IsOdd(a1[1]);
    assert IsOdd(a1[2]);
    var out1 := FindFirstOdd(a1);
    // The postcondition ensures that if out1 is not -1, then a1[out1] is odd and all before are not odd.
    // For out1 == 0, we need to show that forall k :: 0 <= k < 0 ==> !IsOdd(a1[k]) is vacuously true.
    // Also, we need to show that IsOdd(a1[0]) holds, which we already asserted.
    // The verifier may need help to see that the postcondition implies out1 == 0.
    // We can assert the contrapositive: if out1 != 0, then either out1 is -1 or out1 >= 1.
    // But we know a1[0] is odd, so out1 cannot be -1 (since there is an odd).
    // And if out1 >= 1, then by postcondition, forall k :: 0 <= k < out1 ==> !IsOdd(a1[k]).
    // For out1 >= 1, this includes k=0, so !IsOdd(a1[0]), but we have IsOdd(a1[0]) -> contradiction.
    // Therefore out1 must be 0.
    // We can break this down for Dafny:
    if out1 == -1 {
        // Then by postcondition, all elements are not odd, but a1[0] is odd -> contradiction.
        assert forall k :: 0 <= k < a1.Length ==> !IsOdd(a1[k]);
        assert false; // because we know a1[0] is odd
    }
    // Now we know out1 != -1, so by postcondition:
    // 0 <= out1 < a1.Length && IsOdd(a1[out1]) && (forall k :: 0 <= k < out1 ==> !IsOdd(a1[k]))
    // We need to help Dafny see that out1 == 0.
    // We already know a1[0] is odd.
    // If out1 > 0, then the forall includes k=0, so !IsOdd(a1[0]), contradiction.
    // So out1 must be 0.
    // First, assert the postcondition facts:
    // The postcondition is already known to Dafny, but we need to help it use the facts.
    // Instead of asserting the implication, we can use the postcondition directly.
    // Since we know out1 != -1, we can assert the first postcondition holds.
    // Dafny already knows the postconditions, so we can just use them.
    // We'll add an assertion that uses the postcondition to get the bounds.
    assert out1 != -1 ==> (0 <= out1 < a1.Length && IsOdd(a1[out1]) && (forall k :: 0 <= k < out1 ==> !IsOdd(a1[k])));
    // Since we know out1 != -1 from the if block above (if we reached here, out1 != -1 because otherwise we would have asserted false),
    // we can use the implication.
    // Actually, we need to ensure Dafny knows out1 != -1. We can do:
    if out1 == -1 {
        // already handled
    } else {
        // Now we know the postcondition holds for the first case.
        // Dafny should know 0 <= out1 < a1.Length and IsOdd(a1[out1]) and the forall.
        // We can assert these individually to help.
        assert 0 <= out1 < a1.Length;
        assert IsOdd(a1[out1]);
        assert forall k :: 0 <= k < out1 ==> !IsOdd(a1[k]);
        if out1 > 0 {
            // Then k=0 is in the range, so !IsOdd(a1[0])
            assert !IsOdd(a1[0]); // because 0 < out1
            // But we have IsOdd(a1[0]) -> contradiction.
            assert false;
        }
    }
    assert out1 == 0;

    // last
    var a2 := new int[] [2, 4, 1];
    assert a2[0] == 2 && a2[1] == 4 && a2[2] == 1;
    assert !IsOdd(a2[0]);
    assert !IsOdd(a2[1]);
    assert IsOdd(a2[2]);
    var out2 := FindFirstOdd(a2);
    // Similar reasoning: out2 cannot be -1 because a2[2] is odd.
    // If out2 < 2, then by postcondition, a2[out2] is odd and all before are not odd.
    // But if out2 == 0, then a2[0] must be odd, but we have !IsOdd(a2[0]) -> contradiction.
    // If out2 == 1, then a2[1] must be odd, but we have !IsOdd(a2[1]) -> contradiction.
    // Therefore out2 must be 2.
    if out2 == -1 {
        assert forall k :: 0 <= k < a2.Length ==> !IsOdd(a2[k]);
        assert false;
    } else {
        // Use the postcondition
        assert 0 <= out2 < a2.Length;
        assert IsOdd(a2[out2]);
        assert forall k :: 0 <= k < out2 ==> !IsOdd(a2[k]);
        if out2 < 2 {
            if out2 == 0 {
                // Then IsOdd(a2[0]) must hold, but we have !IsOdd(a2[0])
                assert false;
            } else if out2 == 1 {
                // Then IsOdd(a2[1]) must hold, but we have !IsOdd(a2[1])
                assert false;
            }
        }
    }
    assert out2 == 2;

    // none
    var a3 := new int[] [2, 6, 4];
    assert a3[0] == 2 && a3[1] == 6 && a3[2] == 4;
    assert !IsOdd(a3[0]);
    assert !IsOdd(a3[1]);
    assert !IsOdd(a3[2]);
    var out3 := FindFirstOdd(a3);
    // We know all elements are not odd, so by postcondition, if out3 == -1 then the condition holds.
    // But we also need to show that out3 cannot be non-negative, because if it were, then a3[out3] would be odd.
    // But we have for each index that it is not odd.
    // We can assert the universal quantifier to help.
    assert forall k :: 0 <= k < a3.Length ==> !IsOdd(a3[k]);
    // Now, if out3 != -1, then by postcondition, IsOdd(a3[out3]) holds, but we have !IsOdd(a3[out3]) for all k.
    // But we need to be careful: the postcondition only guarantees IsOdd(a3[out3]) if out3 is within bounds.
    // However, if out3 != -1, the postcondition ensures 0 <= out3 < a3.Length.
    // So we can proceed:
    if out3 != -1 {
        assert 0 <= out3 < a3.Length;
        assert IsOdd(a3[out3]);
        // From the universal, we have !IsOdd(a3[out3])
        assert !IsOdd(a3[out3]);
        assert false;
    }
    assert out3 == -1;
}







