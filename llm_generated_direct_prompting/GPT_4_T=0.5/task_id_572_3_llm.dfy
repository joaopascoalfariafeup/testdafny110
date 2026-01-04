// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == SeqFromArray(a)
{
  res := [];
  for i := 0 to a.Length
    invariant res == SeqFromArray(a[..i])
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
    }
  }
}

// Ghost function to convert array to sequence
ghost function SeqFromArray<T>(a: array<T>): seq<T>
  reads a
{
  if a == null then []
  else if a.Length == 0 then []
  else [a[0]] + SeqFromArray(a[1..])
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
