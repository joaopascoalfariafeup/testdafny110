
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function {:fuel 50} MergeSeq(sa: seq<int>, sb: seq<int>): seq<int>
{
  if |sa| == 0 then sb
  else if |sb| == 0 then sa
  else if sa[0] <= sb[0] then [sa[0]] + MergeSeq(sa[1..], sb)
  else [sb[0]] + MergeSeq(sa, sb[1..])
}

lemma SeqAssoc<T>(x: seq<T>, y: seq<T>, z: seq<T>)
{
}







// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures c[..] == MergeSeq(a[..], b[..])
{
    c := new int[a.Length + b.Length];
    var i, j := 0, 0;

    while i < a.Length || j < b.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= j <= b.Length
      invariant c[..i+j] + MergeSeq(a[i..], b[j..]) == MergeSeq(a[..], b[..])
      decreases c.Length - (i + j)
    {
        var oi := i;
        var oj := j;


        if i < a.Length && (j == b.Length  || a[i] <= b[j])  {
            c[j + i] := a[i];




            i := i + 1;
        } 
        else {
            c[i + j] := b[j];



            calc {
              c[..(oi+(oj+1))] + MergeSeq(a[oi..], b[(oj+1)..]);
              == { SeqAssoc(c[..(oi+oj)], [b[oj]], MergeSeq(a[oi..], b[oj+1..])); }
              c[..(oi+oj)] + ([b[oj]] + MergeSeq(a[oi..], b[oj+1..]));
              == { assert c[..oi+oj] + MergeSeq(a[oi..], b[oj..]) == MergeSeq(a[..], b[..]); }
            }

            j := j + 1;
        }
    }


}

lemma MergeSeq_Example_135_24()
  ensures MergeSeq([1,3,5], [2,4]) == [1,2,3,4,5]
{
}

method TestMerge() {
    var a: array<int> := new int[] [1, 3, 5];
    var b: array<int> := new int[] [2, 4]; 
    var c := Merge(a, b);

    assert a[..] == [1,3,5];
    assert b[..] == [2,4];
    MergeSeq_Example_135_24();

    assert c[..] == [1, 2, 3, 4, 5];

    var a2: array<int> := new int[] [1, 5, 3];
    var b2: array<int> := new int[] [4, 2];
    //@invalid var c2 := Merge(a2, b); // violates pre-condition
    //@invalid var c3 := Merge(a, b2); // violates pre-condition 
}
