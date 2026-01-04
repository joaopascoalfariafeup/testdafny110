
method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == ((n*n*n*(n+1)*(n+1)/4) as int) - ((n*(n+1)*(2*n+1)/6) as int)
{
  var sumNumbers := SumNumbers(n);
  var sumCubes := SumCubes(n);
  diff := (sumNumbers*sumNumbers as int) - (sumCubes as int); 
}

method SumCubes(n: nat) returns (s: nat)
  ensures s == n*(n+1)*(2*n+1)/6
{
  s := 0;
  var i := 0;
  while i < n
    invariant i <= n
    invariant s == i*(i+1)*(2*i+1)/6
  {
    i := i + 1;
    s := s + i * i * i;
  }
}

method SumNumbers(n: nat) returns (s: nat)
  ensures s == n*(n+1)/2
{
  s := 0;
  var i : nat := 0;
  while i < n
    invariant i <= n
    invariant s == i*(i+1)/2
  {
    i := i + 1;
    s := s + i;
  }
}

method DifferenceSumCubesAndSumNumbersTest(){
  var res4 := DifferenceSumCubesAndSumNumbers(0);
  assert res4 == 0;

  var res5 := DifferenceSumCubesAndSumNumbers(1);
  assert res5 == 0;

  var res6 := DifferenceSumCubesAndSumNumbers(2);
  assert res6 == 4; 

  var res1:= DifferenceSumCubesAndSumNumbers(3);
  assert res1==36; 
}

