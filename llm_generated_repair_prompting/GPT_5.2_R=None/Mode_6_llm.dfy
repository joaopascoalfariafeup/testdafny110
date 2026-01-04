// Helper predicate to avoid triggerless quantifiers and to simplify specs
ghost predicate InPrefix(a: array<int>, n: int, v: int)
  reads a
  requires a != null
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

lemma CountPrefixBounds(a: array<int>, n: int, v: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures CountPrefix(a, n, v) <= n
{
  // set { j | 0<=j<n && a[j]==v } is a subset of { j | 0<=j<n }
  assert (set j | 0 <= j < n && a[j] == v) <= (set j | 0 <= j < n);
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

  if a[i] == v {
    assert T == S + {i} by {
      assert forall j :: j in T <==> (j in S || j == i);
    }
    assert i !in S;
  } else {
    assert T == S by {
      assert forall j :: j in T <==> j in S;
    }
  }
}

lemma SortedImpliesNoEarlierOccurrence(a: array<int>, i: int)
  requires a != null
  requires 0 < i < a.Length
  requires forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
  requires a[i] != a[i-1]
  ensures forall j :: 0 <= j < i ==> a[j] != a[i]
{
  // In a nondecreasing array, equal values form a contiguous block.
  // If a[i] differs from a[i-1], then a[i] is strictly greater than all earlier elements.
  assert forall j :: 0 <= j < i ==> a[j] <= a[i-1] by
  {
    forall j | 0 <= j < i
      ensures a[j] <= a[i-1]
    {
      var t := j;
      while t < i-1
        invariant j <= t <= i-1
        invariant a[j] <= a[t]
      {
        assert 0 < t+1 < a.Length;
        assert a[t] <= a[t+1];
        t := t + 1;
      }
    }
  }

  // Since a[i] != a[i-1] and nondecreasing, we have a[i-1] < a[i]
  assert a[i-1] < a[i];
  assert forall j :: 0 <= j < i ==> a[j] < a[i] by {
    forall j | 0 <= j < i
      ensures a[j] < a[i]
    {
      assert a[j] <= a[i-1];
      assert a[i-1] < a[i];
    }
  }
}

lemma CountPrefixAtLeast1FromInPrefix(a: array<int>, n: int, v: int)
  requires a != null
  requires 0 <= n <= a.Length
  requires InPrefix(a, n, v)
  ensures CountPrefix(a, n, v) >= 1
{
  var S := set j | 0 <= j < n && a[j] == v;
  assert S != {} by {
    var j :| 0 <= j < n && a[j] == v;
    assert j in S;
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
  requires best_count == CountPrefix(a, i, best_m)
  // best_m is a mode of the prefix a[..i]
  requires forall v :: InPrefix(a, i, v) ==>
            CountPrefix(a, i, best_m) >= CountPrefix(a, i, v)
  // current_count describes the run length ending at i-1
  requires current_count == CountPrefix(a, i, a[i-1])
  // array is sorted
  requires forall k :: 0 < k < a.Length ==> a[k-1] <= a[k]
  ensures
    (if a[i] == a[i-1] then
       (if current_count + 1 > best_count then
          forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v)
        else
          forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v))
     else
       forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v))
{
  if a[i] == a[i-1] {
    CountPrefixIncAt(a, i, a[i]);
    if current_count + 1 > best_count {
      // new best is a[i]
      assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v) by {
        forall v | InPrefix(a, i+1, v)
          ensures CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v)
        {
          if v == a[i] {
          } else {
            CountPrefixIncAt(a, i, v);
            // v's count does not increase at i (since v != a[i])
            assert CountPrefix(a, i+1, v) == CountPrefix(a, i, v);
            // best_m was a mode at i, hence CountPrefix(a,i,v) <= best_count
            if InPrefix(a, i, v) {
              assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
              assert best_count >= CountPrefix(a, i, v);
            } else {
              assert CountPrefix(a, i, v) == 0;
              assert CountPrefix(a, i+1, v) == 0;
            }
            // Count of a[i] after increment is current_count+1 and that exceeds best_count
            assert CountPrefix(a, i+1, a[i]) == current_count + 1;
            assert current_count + 1 > best_count;
            assert CountPrefix(a, i+1, a[i]) > best_count;
            assert CountPrefix(a, i+1, a[i]) >= CountPrefix(a, i+1, v);
          }
        }
      }
    } else {
      // best remains best_m
      assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v) by {
        forall v | InPrefix(a, i+1, v)
          ensures CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v)
        {
          if v == a[i] {
            CountPrefixIncAt(a, i, a[i]);
            assert CountPrefix(a, i+1, a[i]) == current_count + 1;
            // by branch condition, current_count+1 <= best_count == CountPrefix(a,i,best_m)
            assert current_count + 1 <= best_count;
            if best_m == a[i] {
              // then CountPrefix(a,i+1,best_m) == CountPrefix(a,i+1,a[i])
            } else {
              CountPrefixIncAt(a, i, best_m);
              assert CountPrefix(a, i+1, best_m) == CountPrefix(a, i, best_m);
              assert CountPrefix(a, i+1, best_m) == best_count;
              assert CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, a[i]);
            }
          } else {
            CountPrefixIncAt(a, i, v);
            if best_m == a[i] {
              CountPrefixIncAt(a, i, best_m);
              assert CountPrefix(a, i+1, best_m) == CountPrefix(a, i, best_m) + 1;
              if InPrefix(a, i, v) {
                assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
              } else {
                assert CountPrefix(a, i, v) == 0;
              }
              assert CountPrefix(a, i+1, v) == CountPrefix(a, i, v);
            } else {
              CountPrefixIncAt(a, i, best_m);
              assert CountPrefix(a, i+1, best_m) == CountPrefix(a, i, best_m);
              if InPrefix(a, i, v) {
                assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
              } else {
                assert CountPrefix(a, i, v) == 0;
              }
              assert CountPrefix(a, i+1, v) == CountPrefix(a, i, v);
            }
          }
        }
      }
    }
  } else {
    // New value at i; in sorted array it did not occur before.
    SortedImpliesNoEarlierOccurrence(a, i);
    assert !InPrefix(a, i, a[i]) by {
      assert forall j :: 0 <= j < i ==> a[j] != a[i];
    }
    CountPrefixIncAt(a, i, a[i]);
    assert CountPrefix(a, i, a[i]) == 0;
    assert CountPrefix(a, i+1, a[i]) == 1;

    assert forall v :: InPrefix(a, i+1, v) ==> CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v) by {
      forall v | InPrefix(a, i+1, v)
        ensures CountPrefix(a, i+1, best_m) >= CountPrefix(a, i+1, v)
      {
        if v == a[i] {
          // CountPrefix(...,a[i]) == 1 and best_count>=1
          CountPrefixIncAt(a, i, best_m);
          assert CountPrefix(a, i+1, v) == 1;
          assert best_count == CountPrefix(a, i, best_m);
          assert 1 <= best_count;
          // best_m's count in i+1 is at least 1 (since best_m in prefix i)
          assert InPrefix(a, i, best_m);
          assert InPrefix(a, i+1, best_m);
          CountPrefixAtLeast1FromInPrefix(a, i+1, best_m);
          assert CountPrefix(a, i+1, best_m) >= 1;
        } else {
          CountPrefixIncAt(a, i, v);
          CountPrefixIncAt(a, i, best_m);
          if InPrefix(a, i, v) {
            assert CountPrefix(a, i, best_m) >= CountPrefix(a, i, v);
          } else {
            assert CountPrefix(a, i, v) == 0;
          }
          assert CountPrefix(a, i+1, v) == CountPrefix(a, i, v);
          assert CountPrefix(a, i+1, best_m) == CountPrefix(a, i, best_m);
        }
      }
    }
  }
}

// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutions exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a != null
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
      invariant current_count == CountPrefix(a, i, a[i-1])
      invariant best_count == CountPrefix(a, i, best_m)
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

    assert InPrefix(a, a.Length, 1) by { assert a[0] == 1; }
    assert InPrefix(a, a.Length, 2) by { assert a[2] == 2; }
    assert InPrefix(a, a.Length, 3) by { assert a[4] == 3; }

    var c1 := |set j | 0 <= j < a.Length && a[j] == 1|;
    var c2 := |set j | 0 <= j < a.Length && a[j] == 2|;
    var c3 := |set j | 0 <= j < a.Length && a[j] == 3|;

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
      assert (CountPrefix(a, a.Length, m) >= CountPrefix(a, a.Length, 1));
      assert CountPrefix(a, a.Length, 3) >= CountPrefix(a, a.Length, 1);
      assert CountPrefix(a, a.Length, 3) == c3;
      assert CountPrefix(a, a.Length, 1) == c1;
      assert c3 >= c1;
      assert false;
    }

    assert m == 1 || m == 2;
}
