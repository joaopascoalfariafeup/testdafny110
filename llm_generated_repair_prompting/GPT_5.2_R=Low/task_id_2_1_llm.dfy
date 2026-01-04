// Obtains the set of elements (without duplicates) shared between two arrays. 

function SharedFromPrefix<T(==)>(a: array<T>, b: array<T>, n: int): set<T>
  requires 0 <= n <= a.Length
  reads a, b
{
  set x | (exists i:int :: 0 <= i < n && a[i] == x && x in b[..])
}

lemma SharedFromPrefixStep<T(==)>(a: array<T>, b: array<T>, i: int)
  requires 0 <= i < a.Length
  ensures SharedFromPrefix(a, b, i + 1) ==
          (if a[i] in b[..] then SharedFromPrefix(a, b, i) + {a[i]} else SharedFromPrefix(a, b, i))
{
  assert forall x:T ::
    (x in SharedFromPrefix(a, b, i + 1)) <=>
    (x in (if a[i] in b[..] then SharedFromPrefix(a, b, i) + {a[i]} else SharedFromPrefix(a, b, i))) by
  {
    var x: T;

    if a[i] in b[..] {
      assert (x in (SharedFromPrefix(a, b, i) + {a[i]})) <==> (x in SharedFromPrefix(a, b, i) || x == a[i]);
      assert (x in SharedFromPrefix(a, b, i + 1)) <==>
             (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]);
      assert (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]) <==>
             ((exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) || (a[i] == x && x in b[..]));
      assert (x in SharedFromPrefix(a, b, i + 1)) <==> (x in SharedFromPrefix(a, b, i) || x == a[i]);
    } else {
      assert (if a[i] in b[..] then SharedFromPrefix(a, b, i) + {a[i]} else SharedFromPrefix(a, b, i)) == SharedFromPrefix(a, b, i);
      assert (x in SharedFromPrefix(a, b, i + 1)) <==>
             (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]);
      assert (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]) <==>
             ((exists k:int :: 0 <= k < i && a[k] == x && x in b[..]) || (a[i] == x && x in b[..]));
      assert !(a[i] == x && x in b[..]);
      assert (exists k:int :: 0 <= k < i + 1 && a[k] == x && x in b[..]) <==>
             (exists k:int :: 0 <= k < i && a[k] == x && x in b[..]);
      assert (x in SharedFromPrefix(a, b, i + 1)) <==> (x in SharedFromPrefix(a, b, i));
    }
  }
}

method SharedElements<T(==)>(a: array<T>, b: array<T>) returns (result: set<T>)
  ensures result == SharedFromPrefix(a, b, a.Length)
{
  result := {};
  for i := 0 to a.Length // loop through the first array
    invariant 0 <= i <= a.Length
    invariant result == SharedFromPrefix(a, b, i)
  {
    if a[i] !in result && a[i] in b[..] {
      result := result + {a[i]};
    }

    SharedFromPrefixStep(a, b, i);
    assert result == SharedFromPrefix(a, b, i) || result == SharedFromPrefix(a, b, i) + {a[i]};
    if a[i] in b[..] {
      assert result == SharedFromPrefix(a, b, i) + {a[i]};
    } else {
      assert result == SharedFromPrefix(a, b, i);
    }
    assert result == SharedFromPrefix(a, b, i + 1);
  }
}


// Test cases checked statically.
method SharedElementsTest(){
  // arrays with shared elements and no duplicates
  var a1:= new int[] [3, 4, 5, 6];
  var a2:= new int[] [5, 7, 4, 10];
  var res1 := SharedElements(a1, a2);
  assert res1 == {4, 5};

  // arrays with duplicates and shared elements 
  var a3:= new int[] [1, 3, 3, 4];
  var a4:= new int[] [4, 4, 3, 7];
  var res2 := SharedElements(a3, a4);
  assert res2 == {3, 4};

  // arrays with no shared elements
  var a5:= new int[] [11, 12, 13];
  var a6:= new int[] [17, 15, 14];
  var res3 := SharedElements(a5, a6);
  assert res3 == {};
}
