// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

function Max2(x: nat, y: nat): nat {
  if x >= y then x else y
}

function Count(s: seq<int>, v: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else Count(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

function MaxCount(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else Max2(MaxCount(s[..|s|-1]), Count(s, s[|s|-1]))
}

predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma CountAppend(s: seq<int>, x: int, v: int)
  ensures Count(s + [x], v) == Count(s, v) + (if x == v then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountAppend(s[..|s|-1], x, v);
  }
}

lemma CountZeroIfNoOcc(s: seq<int>, v: int)
  requires forall k :: 0 <= k < |s| ==> s[k] != v
  ensures Count(s, v) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountZeroIfNoOcc(s[..|s|-1], v);
  }
}

lemma MaxCountAppend(s: seq<int>, x: int)
  ensures MaxCount(s + [x]) == Max2(MaxCount(s), Count(s + [x], x))
{
}

method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires Sorted(a[..])
  ensures Count(a[..], m) == MaxCount(a[..])
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant Sorted(a[..])
      invariant 1 <= current_count <= i
      invariant 1 <= best_count <= i
      invariant current_count == Count(a[..i], a[i-1])
      invariant best_count == MaxCount(a[..i])
      invariant Count(a[..i], best_m) == best_count
      invariant best_count >= current_count
    {
        ghost var oldBestCount := best_count;
        ghost var oldBestM := best_m;
        ghost var oldPrefix := a[..i];

        if a[i] == a[i-1] {
            current_count := current_count + 1;

            assert a[i] == a[i-1];
            assert Count(a[..i], a[i]) == Count(a[..i], a[i-1]);
            CountAppend(a[..i], a[i], a[i]);
            assert Count(a[..i+1], a[i]) == Count(a[..i], a[i]) + 1;
            assert current_count == Count(a[..i+1], a[i]);

            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            } else {
                // show best_m's count doesn't change
                CountAppend(a[..i], a[i], oldBestM);
                if a[i] == oldBestM {
                    // then Count(a[..i+1], oldBestM) == oldBestCount + 1, contradicting current_count > best_count not taken
                    assert Count(a[..i], oldBestM) == oldBestCount;
                    assert Count(a[..i+1], oldBestM) == oldBestCount + 1;
                    assert current_count == Count(a[..i+1], a[i]);
                    assert a[i] == oldBestM ==> current_count == oldBestCount + 1;
                    assert a[i] == oldBestM ==> current_count > oldBestCount;
                    assert a[i] != oldBestM;
                }
                assert Count(a[..i+1], oldBestM) == oldBestCount;
            }
        }
        else {
            assert a[i] != a[i-1];
            assert a[i] > a[i-1];

            assert forall k :: 0 <= k < i ==> a[k] <= a[i-1];
            assert forall k :: 0 <= k < i ==> a[k] != a[i];
            CountZeroIfNoOcc(a[..i], a[i]);
            assert Count(a[..i], a[i]) == 0;

            current_count := 1;

            CountAppend(a[..i], a[i], a[i]);
            assert Count(a[..i+1], a[i]) == 1;
            assert current_count == Count(a[..i+1], a[i]);
        }

        // update MaxCount/best_count relation for next i
        MaxCountAppend(a[..i], a[i]);
        assert MaxCount(a[..i+1]) == Max2(MaxCount(a[..i]), Count(a[..i+1], a[i]));

        if best_m == a[i] {
          assert Count(a[..i+1], best_m) == Count(a[..i+1], a[i]);
        }

        // Establish best_count == MaxCount(a[..i+1]) and Count(a[..i+1], best_m) == best_count
        if best_count == oldBestCount {
          assert MaxCount(a[..i]) == oldBestCount;
          assert Count(a[..i], oldBestM) == oldBestCount;
          CountAppend(a[..i], a[i], oldBestM);
          if a[i] == oldBestM {
            assert Count(a[..i+1], oldBestM) == oldBestCount + 1;
            assert current_count == Count(a[..i+1], a[i]);
            assert current_count > oldBestCount;
            assert false;
          }
          assert Count(a[..i+1], oldBestM) == oldBestCount;
          assert Count(a[..i+1], best_m) == best_count;
          assert Count(a[..i+1], a[i]) == current_count;
          assert current_count <= best_count;
          assert Max2(MaxCount(a[..i]), Count(a[..i+1], a[i])) == best_count;
          assert MaxCount(a[..i+1]) == best_count;
        } else {
          assert best_count == current_count;
          assert best_m == a[i];
          assert Count(a[..i+1], best_m) == best_count;
          assert MaxCount(a[..i]) == oldBestCount;
          assert oldBestCount < best_count;
          assert Max2(MaxCount(a[..i]), Count(a[..i+1], a[i])) == best_count;
          assert MaxCount(a[..i+1]) == best_count;
        }

        assert best_count >= current_count;
    }
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
