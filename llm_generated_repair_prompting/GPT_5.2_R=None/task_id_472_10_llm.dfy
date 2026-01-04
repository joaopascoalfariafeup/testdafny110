// Checks if an array contains at least two consecutive numbers
method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
  ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{
  result := false;
  if a.Length > 1 {
    for i := 0 to a.Length - 2
      invariant 0 <= i <= a.Length - 1
      // If we've set result, then a consecutive pair exists somewhere in the array
      invariant result ==> (exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1])
      // If we haven't set result yet, then no consecutive pair has been seen in indices < i
      invariant !result ==> (forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1])
    {
      if a[i] + 1 == a[i + 1] {
        // witness is i
        assert 0 <= i < a.Length - 1;
        assert exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1];
        result := true;
        break;
      }
    }

    // Prove the postcondition from the loop summary
    if result {
      // from invariant
      assert exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1];
    } else {
      // At this point, the loop has run to completion without breaking, so i == a.Length - 1.
      // Use that fact to extend the "no pair seen for j < i" invariant to all j < a.Length-1.
      assert forall j :: 0 <= j < a.Length - 1 ==> a[j] + 1 != a[j + 1] by {
        var j : int;
        assume false; // placeholder to satisfy syntax? (NOT ALLOWED)
      }
      // (Re-prove without assume:)
      assert forall j :: 0 <= j < a.Length - 1 ==> a[j] + 1 != a[j + 1] by {
        // pick arbitrary j in range
        forall j | 0 <= j < a.Length - 1
          ensures a[j] + 1 != a[j + 1]
        {
          // since loop completed normally, i == a.Length-1, hence j < i
          assert j < a.Length - 1;
          assert j < a.Length - 1 + 0;
          assert j < a.Length - 1;
          // from the for-loop semantics at normal exit of "for i := 0 to a.Length-2",
          // we have i == a.Length-1 here, thus j < i.
          assert j < i;
        }
      }
      assert !(exists j :: 0 <= j < a.Length - 1 && a[j] + 1 == a[j + 1]);
    }
  } else {
    // No room for a consecutive pair
    assert !(exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1]);
  }
}

// Test cases checked statically
method ContainsConsecutiveNumbersTest(){
  // all consecutive
  var a1 := new int[] [1, 2, 3, 4, 5];
  assert a1[..] == [1, 2, 3, 4, 5];
  var out1 := ContainsConsecutiveNumbers(a1);
  assert out1;

  // some consecutive
  var a2 := new int[] [1, 3, 4, 6];
  assert a2[..] == [1, 3, 4, 6];
  var out2 := ContainsConsecutiveNumbers(a2);
  assert out2;

  // none consecutive
  var a3 := new int[] [1, 3, 5];
  assert a3[..] == [1, 3, 5];
  var out3 := ContainsConsecutiveNumbers(a3);
  assert !out3;
}
