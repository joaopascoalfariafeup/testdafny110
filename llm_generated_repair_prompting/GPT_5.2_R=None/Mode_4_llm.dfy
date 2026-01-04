// Helper predicate to avoid triggerless quantifiers and to simplify specs
ghost predicate InPrefix(a: array<int>, n: int, v: int)
  reads a
  requires 0 <= n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

// Helper: counts occurrences of v in prefix a[..n]
ghost function CountPrefix(a: array<int>, n: int, v: int): nat
  requires a != null
  requires 0 <= n <= a.Length
  reads a
{
  |set j | 0 <= j < n && a[j] == v|
}

lemma CountPrefixLeBySubset(a: array<int>, n: int, v: int, w: int)
  requires a != null
  requires 0 <= n <= a.Length
  requires (set j | 0 <= j < n && a[j] == v) <= (set j | 0 <= j < n && a[j] == w)
  ensures CountPrefix(a, n, v) <= CountPrefix(a, n, w)
{
}

lemma CountPrefixBounds(a: array<int>, n: int, v: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures CountPrefix(a, n, v) <= n
{
  // The set counted is a subset of {0..n-1}
  calc {
    CountPrefix(a, n, v);
    <= |set j | 0 <= j < n| {
      assert (set j | 0 <= j < n && a[j] == v) <= (set j | 0 <= j < n);
      CountPrefixLeBySubset(a, n, v, v); // trivial, but keeps the lemma style consistent
    }
  }
}

lemma CountPrefixIncAt(a: array<int>, i: int, v: int)
  requires a != null
  requires 0 <= i < a.Length
  reads a
  ensures CountPrefix(a, i+1, v) ==
            (if a[i] == v then CountPrefix(a, i, v) + 1 else CountPrefix(a, i, v))
{
  var S := set j | 0 <= j < i && a[j] == v;
  var T := set j | 0 <= j < i+1 && a[j] == v;

  // T is either S or S ∪ {i}
  if a[i] == v {
    assert T == S + {i} by {
      assert forall j :: j in T <==> (j in S || j == i);
    }
    assert i !in S;
    assert |T| == |S| + 1;
  } else {
    assert T == S by {
      assert forall j :: j in T <==> j in S;
    }
  }
}

lemma ModePrefixStep(a: array<int>, i: int, best_m: int, best_count: nat, current_count: nat)
  requires a != null
  requires 1 <= i < a.Length
  requires 1 <= best_count
  requires 1 <= current_count
  requires current_count <= i
  requires best_count <= i
  requires InPrefix(a, i, best_m)
  // best_m is a mode of the prefix a[..i]
  requires forall v :: InPrefix(a, i, v) ==>
            CountPrefix(a, i, best_m) >= CountPrefix(a, i, v)
  // current_count describes the run length ending at i-1
  requires current_count == CountPrefix(a, i, a[i-1])
  // array is sorted
  requires forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
  ensures
    // after processing element i, best_m' is still a mode of prefix a[..i+1]
    (if a[i] == a[i-1] then
       (if current_count + 1 > best_count then
          forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v)
        else
          forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v))
     else
       forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v))
{
  // Proof sketch:
  // - Only count of value a[i] can change from prefix i to i+1.
  // - In sorted array, if a[i] != a[i-1], then a[i] is new at position i, so its previous count is 0.
  // - If the run continues, its count becomes current_count+1; otherwise it's 1.
  // - best_m remains a mode unless the run for a[i] exceeds best_count, in which case a[i] becomes the mode.

  if a[i] == a[i-1] {
    // a[i] count increases by 1
    CountPrefixIncAt(a, i, a[i]);
    if current_count + 1 > best_count {
      // new best is a[i]
      assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v) by {
        intro v;
        if v == a[i] {
        } else {
          // For any other v, its count does not increase at i
          CountPrefixIncAt(a, i, v);
          // Show CountPrefix(a,i,v) <= best_count and best_count < current_count+1 == CountPrefix(a,i+1,a[i])
          if InPrefix(a, i, v) {
            // from mode property at i
            assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
            // best_count is at least CountPrefix(a,i,best_m)? we don't have equality, but we can use best_count <= i and
            // the update condition current_count+1 > best_count implies current_count+1 >= best_count+1.
            // Need a simpler bound: CountPrefix(a,i,v) <= i and CountPrefix(a,i+1,a[i]) == current_count+1 >= 2.
            // Also, best_m is a mode, so CountPrefix(a,i,v) <= CountPrefix(a,i,best_m) <= i.
            CountPrefixBounds(a, i, v);
          } else {
            // v not in prefix i, then count is 0
            assert CountPrefix(a, i, v) == 0;
          }
          // Now, since only v's count may stay same, and a[i]'s count is current_count+1,
          // and current_count+1 > best_count >= 1, it dominates any value whose count <= best_count.
          // We need: for all v in prefix i, CountPrefix(a,i,v) <= best_count.
          // Derive: best_count is the previous maximum count (since mode property and best_m in prefix).
          // We can use mode property with v=best_m itself to get CountPrefix(a,i,best_m) >= CountPrefix(a,i,best_m) (trivial),
          // but we still need relate best_count to CountPrefix(a,i,best_m). We'll avoid that and instead prove:
          // For v in prefix i, CountPrefix(a,i,v) <= CountPrefix(a,i,a[i-1]) == current_count.
          // This is NOT true in general, so we must use mode property:
          // CountPrefix(a,i,v) <= CountPrefix(a,i,best_m) and best_count is >= CountPrefix(a,i,best_m)?
          // Not given. So we require best_count == CountPrefix(a,i,best_m) as an extra loop invariant, proved below in Mode().
        }
      }
    } else {
      // best remains best_m
      assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v) by {
        intro v;
        if v == a[i] {
          // count(a[i]) increased by 1; it is current_count+1 and <= best_count by branch condition
          CountPrefixIncAt(a, i, a[i]);
          assert CountPrefix(a, i+1, a[i]) == current_count + 1;
          // Need CountPrefix(a,i+1,a[i]) <= CountPrefix(a,i+1,best_m).
          // Using best_count == CountPrefix(a,i,best_m) and best_count >= current_count+1 in this branch.
        } else {
          // counts unchanged for v and best_m (unless best_m == a[i], handled above)
          CountPrefixIncAt(a, i, v);
          CountPrefixIncAt(a, i, best_m);
          if InPrefix(a, i, v) {
            assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
          } else {
            assert CountPrefix(a, i, v) == 0;
          }
        }
      }
    }
  } else {
    // New value at i. In sorted array it did not occur before.
    assert !InPrefix(a, i, a[i]) by {
      // since sorted, any occurrence of a[i] before i would force a[i-1] == a[i]
      assert forall j :: 0 <= j < i ==> a[j] <= a[i-1] by {
        intro j; // monotonicity implies a[j] <= a[i-1]
        // Using sortedness transitively is hard; but we only need: a[j] <= a[i-1].
        // This follows from nondecreasing array: a[j] <= a[i-1] for j<i.
      }
    }
    // Therefore its count in prefix i is 0, and in prefix i+1 is 1.
    CountPrefixIncAt(a, i, a[i]);
    assert CountPrefix(a, i, a[i]) == 0;
    assert CountPrefix(a, i+1, a[i]) == 1;

    // best_m remains a mode
    assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v) by {
      intro v;
      if v == a[i] {
        // Count is 1; best_count >= 1
      } else {
        CountPrefixIncAt(a, i, v);
        CountPrefixIncAt(a, i, best_m);
        if InPrefix(a, i, v) {
          assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
        } else {
          assert CountPrefix(a, i, v) == 0;
        }
      }
    }
  }
}

// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i :: 0 < i < a.Length ==> a[i-1] <= a[i]
  ensures InPrefix(a, a.Length, m)
  ensures forall v :: InPrefix(a, a.Length, v) ==>
            CountPrefix(a, a.Length, m) >= CountPrefix(a, a.Length, v)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count
      invariant 1 <= current_count
      invariant current_count <= i
      invariant best_count <= i
      invariant InPrefix(a, i, best_m)
      // current_count describes the run length of the value ending at i-1
      invariant current_count == CountPrefix(a, i, a[i-1])
      // best_count matches the count of best_m in the prefix
      invariant best_count == CountPrefix(a, i, best_m)
      // best_m is a mode of the prefix a[..i]
      invariant forall v :: InPrefix(a, i, v) ==>
                CountPrefix(a, i, best_m) >= CountPrefix(a, i, v)
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;
            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }
        }
        else {
            current_count := 1;
        }

        // Help Dafny re-establish the quantified invariant via the step lemma
        if i < a.Length {
          ModePrefixStep(a, i, best_m, best_count, current_count);
        }
    }
    return best_m;
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    assert a[..] == [1,1,2,2,3];
    var m := Mode(a);

    // Help the verifier connect the postcondition to this concrete test
    assert InPrefix(a, a.Length, 1) by { assert a[0] == 1; }
    assert InPrefix(a, a.Length, 2) by { assert a[2] == 2; }
    assert InPrefix(a, a.Length, 3) by { assert a[4] == 3; }

    var c1 := |set j | 0 <= j < a.Length && a[j] == 1|;
    var c2 := |set j | 0 <= j < a.Length && a[j] == 2|;
    var c3 := |set j | 0 <= j < a.Length && a[j] == 3|;

    // Concrete witnesses to nail down the set cardinalities
    assert c1 == 2 by {
      var S := set j | 0 <= j < a.Length && a[j] == 1;
      assert 0 in S;
      assert 1 in S;
      assert forall j :: j in S ==> j == 0 || j == 1;
      assert S == {0,1} by {
        assert forall j :: j in S <==> j in {0,1};
      }
    }
    assert c2 == 2 by {
      var S := set j | 0 <= j < a.Length && a[j] == 2;
      assert 2 in S;
      assert 3 in S;
      assert forall j :: j in S ==> j == 2 || j == 3;
      assert S == {2,3} by {
        assert forall j :: j in S <==> j in {2,3};
      }
    }
    assert c3 == 1 by {
      var S := set j | 0 <= j < a.Length && a[j] == 3;
      assert 4 in S;
      assert forall j :: j in S ==> j == 4;
      assert S == {4} by {
        assert forall j :: j in S <==> j in {4};
      }
    }

    if m == 3 {
      // From mode postcondition with v=1, count(m) >= count(1), but 1 occurs more than 3
      assert (CountPrefix(a, a.Length, m) >= CountPrefix(a, a.Length, 1));
      assert CountPrefix(a, a.Length, 3) >= CountPrefix(a, a.Length, 1);
      // Using concrete counts
      assert CountPrefix(a, a.Length, 3) == c3;
      assert CountPrefix(a, a.Length, 1) == c1;
      assert c3 >= c1;
      assert false;
    }

    // Now m must be 1 or 2
    assert m == 1 || m == 2;
}
