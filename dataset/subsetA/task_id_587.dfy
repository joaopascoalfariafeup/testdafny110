// Converts an array to a sequence
method ArrayToSeq<T>(a: array<T>) returns (s: seq<T>)
  ensures s == a[..]
{
  s := [];
  for i := 0 to a.Length
    invariant s == a[..i]
  {
    s := s + [a[i]];
  }
}

method ArrayToSeqTest(){
  var a1 := new int[] [5, 10, 7, 4, 15, 3];
  var res1 := ArrayToSeq(a1);
  assert res1 == [5, 10, 7, 4, 15, 3];
}
