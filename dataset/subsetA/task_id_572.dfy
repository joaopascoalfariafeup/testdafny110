// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == DeDup(a[..])
{
  res := [];
  for i := 0 to a.Length
    invariant res == DeDup(a[..i])
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]]; // proof helper
  }
  assert a[..] == a[..a.Length]; // proof helper
}

// Returns a sequence with all the duplicates removed from the input sequence
// (keeping the first occurrence of each element).
ghost function {:fuel 4}DeDup<T(==)>(s: seq<T>): (result: seq<T>) {
  if |s| <= 1 then s
  else if Last(s) in DropLast(s) then DeDup(DropLast(s))
  else DeDup(DropLast(s)) + [Last(s)]
}

// Auxiliary function that gives the last element of a non-empty sequence
ghost function Last<T>(a: seq<T>): T
  requires |a| > 0
{
  a[|a| - 1]
}

// Auxiliary function that gives a sequence without the last element.
ghost function DropLast<T>(a: seq<T>): seq<T>
  requires |a| > 0
{
  a[0..|a| - 1]
}

// Test cases checked statically
method RemoveDuplicatesTest(){
  var a1 := new int[] [1, 2, 1, 2];
  var res1 := RemoveDuplicates(a1);
  assert res1 == [1, 2];

  var a2:= new int[] [1, 1, 1];
  var res2 := RemoveDuplicates(a2);
  assert res2 == [1];
}