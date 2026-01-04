// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
  ensures exists k :: 0 <= k < a.Length && a[k] == m
  ensures forall k :: 0 <= k < a.Length ==> Count(a[..], a[k]) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant 0 <= current_count <= i
      invariant current_count == Count(a[i-current_count..i], a[i-1])
      invariant best_count == Count(a[..i], best_m)
      invariant forall k :: 0 <= k < i ==> Count(a[..i], a[k]) <= best_count
      invariant exists k :: 0 <= k < i && a[k] == best_m
    {
        if i < a.Length {
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
        }
    }
    m := best_m;
}

function {:fuel 5} Count(s: seq<int>, x: int): int
  ensures Count(s, x) >= 0
  ensures forall i :: 0 <= i < |s| && s[i] == x ==> Count(s, x) > 0
  ensures Count(s, x) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] != x
  ensures Count(s, x) == Count(s[..|s|], x)
{
  if |s| == 0 then 0 else (if s[|s|-1] == x then 1 else 0) + Count(s[..|s|-1], x)
}

lemma CountLemma(s: seq<int>, x: int, i: int)
  requires 0 <= i < |s|
  requires forall j, k :: 0 <= j <= k < |s| ==> s[j] <= s[k]
  ensures Count(s[..i+1], x) >= Count(s[..i], x)
{
  // Proof by cases on whether s[i] == x
  if s[i] == x {
    // If s[i] == x, then Count(s[..i+1], x) = Count(s[..i], x) + 1
    // So the inequality holds
  } else {
    // If s[i] != x, then Count(s[..i+1], x) = Count(s[..i], x)
    // So the inequality holds as equality
  }
}

lemma CountMonotonic(s: seq<int>, x: int, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures Count(s[..i], x) <= Count(s[..j], x)
{
  if i == j {
    // trivial
  } else {
    // Recursive proof
    CountMonotonic(s, x, i, j-1);
    // Now we know Count(s[..i], x) <= Count(s[..j-1], x)
    // And Count(s[..j], x) >= Count(s[..j-1], x) by CountLemma
    // So Count(s[..i], x) <= Count(s[..j], x)
  }
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    // Helper assertions to prove test outcome
    assert a[..] == [1, 1, 2, 2, 3];
    // Prove Count values with explicit computation
    // First compute Count for the entire sequence
    assert Count([1, 1, 2, 2, 3], 1) == 2 by {
      calc {
        Count([1, 1, 2, 2, 3], 1);
        == // Unfold definition
        (if [1, 1, 2, 2, 3][4] == 1 then 1 else 0) + Count([1, 1, 2, 2, 3][..4], 1);
        == { assert [1, 1, 2, 2, 3][4] == 3; }
        0 + Count([1, 1, 2, 2, 3][..4], 1);
        == { assert [1, 1, 2, 2, 3][..4] == [1, 1, 2, 2]; }
        Count([1, 1, 2, 2], 1);
        == // Unfold again
        (if [1, 1, 2, 2][3] == 1 then 1 else 0) + Count([1, 1, 2, 2][..3], 1);
        == { assert [1, 1, 2, 2][3] == 2; }
        0 + Count([1, 1, 2, 2][..3], 1);
        == { assert [1, 1, 2, 2][..3] == [1, 1, 2]; }
        Count([1, 1, 2], 1);
        == // Unfold
        (if [1, 1, 2][2] == 1 then 1 else 0) + Count([1, 1, 2][..2], 1);
        == { assert [1, 1, 2][2] == 2; }
        0 + Count([1, 1, 2][..2], 1);
        == { assert [1, 1, 2][..2] == [1, 1]; }
        Count([1, 1], 1);
        == // Unfold
        (if [1, 1][1] == 1 then 1 else 0) + Count([1, 1][..1], 1);
        == { assert [1, 1][1] == 1; }
        1 + Count([1, 1][..1], 1);
        == { assert [1, 1][..1] == [1]; }
        1 + Count([1], 1);
        == // Unfold
        1 + ((if [1][0] == 1 then 1 else 0) + Count([1][..0], 1));
        == { assert [1][0] == 1; }
        1 + (1 + Count([1][..0], 1));
        == { assert [1][..0] == []; }
        1 + (1 + Count([], 1));
        == { assert Count([], 1) == 0; }
        1 + (1 + 0);
        ==
        2;
      }
    }
    
    assert Count([1, 1, 2, 2, 3], 2) == 2 by {
      calc {
        Count([1, 1, 2, 2, 3], 2);
        ==
        (if [1, 1, 2, 2, 3][4] == 2 then 1 else 0) + Count([1, 1, 2, 2, 3][..4], 2);
        == { assert [1, 1, 2, 2, 3][4] == 3; }
        0 + Count([1, 1, 2, 2, 3][..4], 2);
        == { assert [1, 1, 2, 2, 3][..4] == [1, 1, 2, 2]; }
        Count([1, 1, 2, 2], 2);
        ==
        (if [1, 1, 2, 2][3] == 2 then 1 else 0) + Count([1, 1, 2, 2][..3], 2);
        == { assert [1, 1, 2, 2][3] == 2; }
        1 + Count([1, 1, 2, 2][..3], 2);
        == { assert [1, 1, 2, 2][..3] == [1, 1, 2]; }
        1 + Count([1, 1, 2], 2);
        ==
        1 + ((if [1, 1, 2][2] == 2 then 1 else 0) + Count([1, 1, 2][..2], 2));
        == { assert [1, 1, 2][2] == 2; }
        1 + (1 + Count([1, 1, 2][..2], 2));
        == { assert [1, 1, 2][..2] == [1, 1]; }
        1 + (1 + Count([1, 1], 2));
        ==
        1 + (1 + ((if [1, 1][1] == 2 then 1 else 0) + Count([1, 1][..1], 2)));
        == { assert [1, 1][1] == 1; }
        1 + (1 + (0 + Count([1, 1][..1], 2)));
        == { assert [1, 1][..1] == [1]; }
        1 + (1 + Count([1], 2));
        ==
        1 + (1 + ((if [1][0] == 2 then 1 else 0) + Count([1][..0], 2)));
        == { assert [1][0] == 1; }
        1 + (1 + (0 + Count([1][..0], 2)));
        == { assert [1][..0] == []; }
        1 + (1 + Count([], 2));
        == { assert Count([], 2) == 0; }
        1 + (1 + 0);
        ==
        2;
      }
    }
    
    assert Count([1, 1, 2, 2, 3], 3) == 1 by {
      calc {
        Count([1, 1, 2, 2, 3], 3);
        ==
        (if [1, 1, 2, 2, 3][4] == 3 then 1 else 0) + Count([1, 1, 2, 2, 3][..4], 3);
        == { assert [1, 1, 2, 2, 3][4] == 3; }
        1 + Count([1, 1, 2, 2, 3][..4], 3);
        == { assert [1, 1, 2, 2, 3][..4] == [1, 1, 2, 2]; }
        1 + Count([1, 1, 2, 2], 3);
        ==
        1 + ((if [1, 1, 2, 2][3] == 3 then 1 else 0) + Count([1, 1, 2, 2][..3], 3));
        == { assert [1, 1, 2, 2][3] == 2; }
        1 + (0 + Count([1, 1, 2, 2][..3], 3));
        == { assert [1, 1, 2, 2][..3] == [1, 1, 2]; }
        1 + Count([1, 1, 2], 3);
        ==
        1 + ((if [1, 1, 2][2] == 3 then 1 else 0) + Count([1, 1, 2][..2], 3));
        == { assert [1, 1, 2][2] == 2; }
        1 + (0 + Count([1, 1, 2][..2], 3));
        == { assert [1, 1, 2][..2] == [1, 1]; }
        1 + Count([1, 1], 3);
        ==
        1 + ((if [1, 1][1] == 3 then 1 else 0) + Count([1, 1][..1], 3));
        == { assert [1, 1][1] == 1; }
        1 + (0 + Count([1, 1][..1], 3));
        == { assert [1, 1][..1] == [1]; }
        1 + Count([1], 3);
        ==
        1 + ((if [1][0] == 3 then 1 else 0) + Count([1][..0], 3));
        == { assert [1][0] == 1; }
        1 + (0 + Count([1][..0], 3));
        == { assert [1][..0] == []; }
        1 + Count([], 3);
        == { assert Count([], 3) == 0; }
        1 + 0;
        ==
        1;
      }
    }
    
    // Now we know the counts: 1 appears 2 times, 2 appears 2 times, 3 appears 1 time
    // So m must be either 1 or 2
    assert m == 1 || m == 2;
}

