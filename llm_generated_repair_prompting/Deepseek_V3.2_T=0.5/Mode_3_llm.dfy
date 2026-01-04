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
{
  if |s| == 0 then 0 else (if s[|s|-1] == x then 1 else 0) + Count(s[..|s|-1], x)
}

lemma CountLemma(s: seq<int>, x: int, i: int)
  requires 0 <= i < |s|
  requires forall j, k :: 0 <= j <= k < |s| ==> s[j] <= s[k]
  ensures Count(s[..i+1], x) >= Count(s[..i], x)
{
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    // Helper assertions to prove test outcome
    assert a[..] == [1, 1, 2, 2, 3];
    // Prove Count values with explicit computation
    calc {
      Count([1, 1, 2, 2, 3], 1);
      == { assert [1, 1, 2, 2, 3][..] == [1, 1, 2, 2, 3]; }
      Count([1, 1, 2, 2, 3][..], 1);
      == { assert [1, 1, 2, 2, 3][4] == 3; assert [1, 1, 2, 2, 3][3] == 2; 
           assert [1, 1, 2, 2, 3][2] == 2; assert [1, 1, 2, 2, 3][1] == 1; 
           assert [1, 1, 2, 2, 3][0] == 1; }
      2;
    }
    assert Count([1, 1, 2, 2, 3], 1) == 2;
    calc {
      Count([1, 1, 2, 2, 3], 2);
      == { assert [1, 1, 2, 2, 3][..] == [1, 1, 2, 2, 3]; }
      Count([1, 1, 2, 2, 3][..], 2);
      == { assert [1, 1, 2, 2, 3][4] == 3; assert [1, 1, 2, 2, 3][3] == 2; 
           assert [1, 1, 2, 2, 3][2] == 2; assert [1, 1, 2, 2, 3][1] == 1; 
           assert [1, 1, 2, 2, 3][0] == 1; }
      2;
    }
    assert Count([1, 1, 2, 2, 3], 2) == 2;
    calc {
      Count([1, 1, 2, 2, 3], 3);
      == { assert [1, 1, 2, 2, 3][..] == [1, 1, 2, 2, 3]; }
      Count([1, 1, 2, 2, 3][..], 3);
      == { assert [1, 1, 2, 2, 3][4] == 3; assert [1, 1, 2, 2, 3][3] == 2; 
           assert [1, 1, 2, 2, 3][2] == 2; assert [1, 1, 2, 2, 3][1] == 1; 
           assert [1, 1, 2, 2, 3][0] == 1; }
      1;
    }
    assert Count([1, 1, 2, 2, 3], 3) == 1;
    assert m == 1 || m == 2;
}


