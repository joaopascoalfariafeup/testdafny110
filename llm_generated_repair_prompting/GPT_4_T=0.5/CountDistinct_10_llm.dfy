
// Returns the number of distinct elements in a sorted array of integers.
ghost function seqc(a: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j] // The sequence is sorted in non-decreasing order
{
  if |a| == 0 then []
  else if a[|a|-1] != a[|a|-2] then seqc(a[..|a|-1]) + [1]
  else seqc(a[..|a|-1]) + [0]
}

// Returns the sum of the elements in a sequence.
ghost function sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum(s[1..])
}

method CountDistinct(a: array<int>) returns (count: nat)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] // The array is sorted in non-decreasing order
  ensures 0 <= count <= a.Length // The count of distinct elements is always between 0 and the length of the array
  ensures forall i, j :: 0 <= i < j < a.Length && a[i] != a[j] ==> count > 0 // If there are distinct elements, count is more than 0
  ensures count == (if a.Length == 0 then 0 else 1) + sum(seqc(a[..])[1..]) // Count is the sum of distinct elements
{
    if a.Length == 0 {
        return 0;
    }
    count := 1;
    for i := 1 to a.Length
      invariant 1 <= count <= i + 1 // Count is always between 1 and i+1
      invariant count == (if i == 0 then 0 else 1) + sum(seqc(a[..i])[1..i]) // Count is equal to the number of distinct elements in the sub-array from index 0 to i
    {
        if a[i] != a[i-1] {
            count := count + 1;
        }
        else {
        }
    }
    return count;
}

method TestCountDistinct() {
    var a := new int[] [1, 1, 2, 2, 3];
    var count := CountDistinct(a);
    assert count == 3;
}

