// Takes an array of integers and returns an array of the sums of 
// each pair of adjacent elements.
method PairwiseAddition(a: array<int>) returns (result: array<int>)
  ensures result.Length == a.Length / 2
  ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
{
  result := new int[a.Length / 2];
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant result.Length == a.Length / 2
    invariant forall j :: 0 <= j < i ==> result[j] == a[2*j] + a[2*j + 1]
  {
    result[i] := a[2*i] + a[2*i + 1];
    i := i + 1;
  }
}

method PairwiseAdditionTest(){
  var s1 := new int[] [1, 5, 7, 8];
  var res1 := PairwiseAddition(s1);
  assert res1[..] == [6, 15];

  var s2 := new int[] [2, 6, 8, 9];
  var res2 := PairwiseAddition(s2);
  assert res2[..] == [8, 17];
}

