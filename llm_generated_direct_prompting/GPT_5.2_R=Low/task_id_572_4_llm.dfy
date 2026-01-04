// Returns a sequence with all the duplicates removed from the input array
// (keeping the first occurrence of each element).
function SpecRemoveDuplicatesPrefix<T(==)>(a: array<T>, n: int): seq<T>
  requires 0 <= n <= a.Length
  reads a
  decreases n
{
  if n == 0 then
    []
  else
    var i := n - 1;
    if a[i] !in a[..i] then
      SpecRemoveDuplicatesPrefix(a, i) + [a[i]]
    else
      SpecRemoveDuplicatesPrefix(a, i)
}

function SpecRemoveDuplicates<T(==)>(a: array<T>): seq<T>
  reads a
{
  SpecRemoveDuplicatesPrefix(a, a.Length)
}

method RemoveDuplicates<T(==)>(a: array<T>)  returns (res: seq<T>)
  ensures res == SpecRemoveDuplicates(a)
{
  res := [];
  for i := 0 to a.Length
    invariant res == SpecRemoveDuplicatesPrefix(a, i)
  {
    if a[i] !in a[..i] {
      res := res + [a[i]];
      assert SpecRemoveDuplicatesPrefix(a, i + 1) == SpecRemoveDuplicatesPrefix(a, i) + [a[i]];
    } else {
      assert SpecRemoveDuplicatesPrefix(a, i + 1) == SpecRemoveDuplicatesPrefix(a, i);
    }
  }
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
