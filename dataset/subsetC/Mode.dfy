// Returns the mode (element with highest frequency) in a non-empty sorted array.
// In case multiple solutins exist, returns an arbitrary one.
method Mode(a: array<int>) returns (m: int)
  requires IsSorted(a)
  requires a.Length > 0
  ensures m in a[..]
  ensures forall k :: 0 <= k < a.Length ==> Count(a[..], a[k]) <= Count(a[..], m)
{
    var best_m := a[0];
    var best_count := 1;
    var current_count := 1;
    for i := 1 to a.Length 
        invariant best_m in a[..i]
        invariant best_count == Count(a[..i], best_m)
        invariant forall k :: 0 <= k < i ==> Count(a[..i], a[k]) <= best_count
        invariant current_count == Count(a[..i], a[i-1])
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
        assert a[..i+1] == a[..i] + [a[i]]; // helper
    }
    assert a[..] == a[..a.Length]; // helper
    return best_m;
}

// Counts the number of occurrences of a value in a sequence
ghost function {:fuel 5} Count<T>(s: seq<T>, x: T) : nat
  ensures x !in s ==> Count(s, x) == 0
{
    if |s| == 0 then 0 else (if s[|s|-1] == x then 1 else 0) + Count(s[..|s|-1], x)
}

// Checks if the array is sorted
ghost predicate IsSorted(a: array<int>) 
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


method TestMode() {
    var a := new int[] [1, 1, 2, 2, 3];
    var m := Mode(a);
    assert a[..] == [1] + [1] + [2] + [2] + [3]; // helper
    assert m == 1 || m == 2;

    var unsorted := new int[] [3, 1, 3];
    var m2 := Mode(unsorted); // violates pre-condition

}