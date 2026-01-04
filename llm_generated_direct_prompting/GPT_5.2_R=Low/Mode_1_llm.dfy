// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
predicate Sorted(s: seq<int>)
{
  forall i:int, j:int :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function CountSeq(s: seq<int>, v: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountSeq(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

lemma CountSeqAppendOne(s: seq<int>, x: int, v: int)
  ensures CountSeq(s + [x], v) == CountSeq(s, v) + (if x == v then 1 else 0)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountSeqAppendOne(s[..|s|-1], x, v);
  }
}

method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires Sorted(a[..])
  ensures m in a[..]
  ensures forall v:int :: v in a[..] ==> CountSeq(a[..], v) <= CountSeq(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
      invariant 1 <= i <= a.Length
      invariant 1 <= best_count <= i
      invariant 1 <= current_count <= i
      invariant best_m in a[..i]
      invariant CountSeq(a[..i], best_m) == best_count
      invariant forall v:int :: v in a[..i] ==> CountSeq(a[..i], v) <= best_count
      invariant forall j:int :: 0 <= j < current_count ==> a[i-1-j] == a[i-1]
      invariant i - current_count == 0 || a[i - current_count - 1] != a[i-1]
    {
        if a[i] == a[i-1] {
            current_count := current_count + 1;

            assert forall j:int :: 0 <= j < current_count ==> a[i-j] == a[i];
            assert i + 1 - current_count == 0 || a[i + 1 - current_count - 1] != a[i];

            if current_count > best_count {
                best_count := current_count;
                best_m := a[i];
            }

            CountSeqAppendOne(a[..i], a[i], best_m);
            assert CountSeq(a[..i+1], best_m) == CountSeq(a[..i], best_m) + (if a[i] == best_m then 1 else 0);
            assert CountSeq(a[..i+1], best_m) == best_count;

            assert forall v:int :: v in a[..i+1] ==> CountSeq(a[..i+1], v) <= best_count by {
              var v:int;
              assume v in a[..i+1];
              if v in a[..i] {
                CountSeqAppendOne(a[..i], a[i], v);
                if a[i] == v {
                  assert CountSeq(a[..i+1], v) == CountSeq(a[..i], v) + 1;
                  assert CountSeq(a[..i], v) <= best_count - 1 || best_count == 1;
                  if v == best_m {
                    assert CountSeq(a[..i+1], v) == best_count;
                  } else {
                    assert CountSeq(a[..i], v) <= best_count;
                    assert CountSeq(a[..i+1], v) <= best_count + 1;
                    assert CountSeq(a[..i+1], v) <= best_count;
                  }
                } else {
                  assert CountSeq(a[..i+1], v) == CountSeq(a[..i], v);
                  assert CountSeq(a[..i+1], v) <= best_count;
                }
              } else {
                assert v == a[i];
                CountSeqAppendOne(a[..i], a[i], v);
                assert CountSeq(a[..i+1], v) == CountSeq(a[..i], v) + 1;
                assert CountSeq(a[..i+1], v) == current_count;
                assert current_count <= best_count;
                assert CountSeq(a[..i+1], v) <= best_count;
              }
            }
        }
        else {
            current_count := 1;

            assert forall j:int :: 0 <= j < current_count ==> a[i-j] == a[i];
            assert i + 1 - current_count == 0 || a[i + 1 - current_count - 1] != a[i];

            CountSeqAppendOne(a[..i], a[i], best_m);
            assert a[i] != best_m ==> CountSeq(a[..i+1], best_m) == CountSeq(a[..i], best_m);
            assert a[i] != best_m ==> CountSeq(a[..i+1], best_m) == best_count;

            assert forall v:int :: v in a[..i+1] ==> CountSeq(a[..i+1], v) <= best_count by {
              var v:int;
              assume v in a[..i+1];
              if v in a[..i] {
                CountSeqAppendOne(a[..i], a[i], v);
                if a[i] == v {
                  assert false;
                } else {
                  assert CountSeq(a[..i+1], v) == CountSeq(a[..i], v);
                  assert CountSeq(a[..i+1], v) <= best_count;
                }
              } else {
                assert v == a[i];
                CountSeqAppendOne(a[..i], a[i], v);
                assert CountSeq(a[..i+1], v) == CountSeq(a[..i], v) + 1;
                assert CountSeq(a[..i], v) == 0;
                assert CountSeq(a[..i+1], v) == 1;
                assert CountSeq(a[..i+1], v) <= best_count;
              }
            }
        }
    }
    assert best_m in a[..a.Length];
    assert forall v:int :: v in a[..a.Length] ==> CountSeq(a[..a.Length], v) <= CountSeq(a[..a.Length], best_m);
    return best_m;
}




method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;
}
