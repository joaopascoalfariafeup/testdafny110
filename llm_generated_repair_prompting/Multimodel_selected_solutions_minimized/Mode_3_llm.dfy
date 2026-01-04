// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.

predicate Sorted(s: seq<int>)
{
  forall i: nat, j: nat :: i < j < |s| ==> s[i] <= s[j]
}

function MaxNat(x: nat, y: nat): nat
{
  if x >= y then x else y
}


function RunLenEndingAt(s: seq<int>, n: nat): nat
  requires 0 < n <= |s|
{
  if n == 1 then 1
  else if s[n-1] == s[n-2] then 1 + RunLenEndingAt(s, n-1)
  else 1
}

function MaxRunLen(s: seq<int>, n: nat): nat
  requires n <= |s|
  decreases n
{
  if n == 0 then 0
  else MaxNat(MaxRunLen(s, n-1), RunLenEndingAt(s, n))
}


method Mode(a: array<int>) returns (m: int)
  requires a.Length > 0
  requires Sorted(a[..a.Length])
  ensures exists k: nat :: 1 <= k <= a.Length && a[k-1] == m && RunLenEndingAt(a[..a.Length], k) == MaxRunLen(a[..a.Length], a.Length)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    var s := a[..a.Length];
    for i := 1 to a.Length
      invariant current_count == RunLenEndingAt(s, i)
      invariant best_count == MaxRunLen(s, i)
      invariant exists k: nat :: 1 <= k <= i && s[k-1] == best_m && RunLenEndingAt(s, k) == best_count
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
    }


    return best_m;
}

method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert m == 1 || m == 2;

    var unsorted := new int[] [3, 1, 3];
    //@invalid var m2 := Mode(unsorted); // violates pre-condition
}