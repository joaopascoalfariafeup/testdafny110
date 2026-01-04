ghost predicate ConsecutiveAt(a: array<int>, i: int)
  reads a
{
  0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1]
}

lemma ConsecutiveAtImpliesExists(a: array<int>, i: int)
  requires 0 <= i < a.Length - 1
  requires ConsecutiveAt(a, i)
  ensures exists j :: 0 <= j < a.Length - 1 && ConsecutiveAt(a, j)
{
  // provide an explicit witness
  assert exists j :: j == i && 0 <= j < a.Length - 1 && ConsecutiveAt(a, j);
}

// Checks if an array contains at least two consecutive numbers
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    modifies {} // important: the method does not change the heap, so callers can rely on pre-call facts about `a`
    ensures a[..] == old(a[..]) // make heap-nonmodification usable to callers for facts about elements
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && ConsecutiveAt(a, i))
{
    result := false;
    if a.Length > 0 {
        for i := 0 to a.Length - 1
            invariant 0 <= i <= a.Length - 1
            invariant !result ==> (forall j :: 0 <= j < i ==> !ConsecutiveAt(a, j))
            invariant result ==> (exists j :: 0 <= j < i && ConsecutiveAt(a, j))
        {
            // From the for-loop range, we have i < a.Length - 1, so i+1 is in-bounds
            assert 0 <= i < a.Length - 1;

            if a[i] + 1 == a[i + 1] {
                // Connect the raw array expression to ConsecutiveAt
                assert ConsecutiveAt(a, i);
                result := true;

                // Establish the "result ==> exists j < i" loop invariant for the next loop point
                assert exists j :: 0 <= j < i + 1 && ConsecutiveAt(a, j);

                break;
            }
        }
    }
}

// Test cases checked statically
method ContainsConsecutiveNumbersTest(){
    // all consecutive
    var a1 := new int[] [1, 2, 3, 4, 5];
    assert a1[..] == [1, 2, 3, 4, 5];
    assert ConsecutiveAt(a1, 0);
    ConsecutiveAtImpliesExists(a1, 0);
    // Help Dafny with an explicit witness for the existential
    assert 0 <= 0 < a1.Length - 1;
    assert exists i :: i == 0 && 0 <= i < a1.Length - 1 && ConsecutiveAt(a1, i);
    assert (exists i :: 0 <= i < a1.Length - 1 && ConsecutiveAt(a1, i));
    var out1 := ContainsConsecutiveNumbers(a1);
    // Re-establish the concrete array facts after the call (heap unchanged)
    assert a1[..] == [1, 2, 3, 4, 5];
    assert (exists i :: 0 <= i < a1.Length - 1 && ConsecutiveAt(a1, i));
    // Help Dafny apply the postcondition to this concrete call
    assert out1 <==> (exists i :: 0 <= i < a1.Length - 1 && ConsecutiveAt(a1, i));
    assert out1;

    // some consecutive
    var a2 := new int[] [1, 3, 4, 6];
    assert a2[..] == [1, 3, 4, 6];
    assert ConsecutiveAt(a2, 1);
    ConsecutiveAtImpliesExists(a2, 1);
    // Help Dafny with an explicit witness for the existential
    assert 0 <= 1 < a2.Length - 1;
    assert exists i :: i == 1 && 0 <= i < a2.Length - 1 && ConsecutiveAt(a2, i);
    assert (exists i :: 0 <= i < a2.Length - 1 && ConsecutiveAt(a2, i));
    var out2 := ContainsConsecutiveNumbers(a2);
    // Re-establish the concrete array facts after the call (heap unchanged)
    assert a2[..] == [1, 3, 4, 6];
    assert (exists i :: 0 <= i < a2.Length - 1 && ConsecutiveAt(a2, i));
    // Help Dafny apply the postcondition to this concrete call
    assert out2 <==> (exists i :: 0 <= i < a2.Length - 1 && ConsecutiveAt(a2, i));
    assert out2;

    // none consecutive
    var a3 := new int[] [1, 3, 5];
    assert a3[..] == [1, 3, 5];
    assert forall i :: 0 <= i < a3.Length - 1 ==> !ConsecutiveAt(a3, i);
    var out3 := ContainsConsecutiveNumbers(a3);
    assert !out3;
}

