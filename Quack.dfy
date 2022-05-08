class Quack
{
    var buf:array<char>;
    var m:int, n:int;

    ghost var shadow: seq<char>;

    predicate Valid() reads this, this.buf
    { buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int)
    requires size > 0;
    ensures shadow == []
    ensures fresh(buf)
    ensures Valid()
    {
        buf := new char[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    method Empty() returns (x: bool)
    requires Valid();
    ensures x <==> shadow==[] // an empty shadow means x is true
    ensures Valid()           // can be better to make this last
    {
       x := m==n;             // no elements means x is true
    }      

    method Push(x: char) modifies this, this.buf, this`m, this`n
    requires Valid();
    // code
    ensures if old(n)   == old(buf.Length) then fresh(buf) else buf==old(buf)
    ensures if old(n-m) == old(buf.Length) then buf.Length==2*old(buf.Length) else buf.Length==old(buf.Length)
    ensures 0<n<=buf.Length ==> buf[n-1]==x
    // shadow
    ensures |shadow|    == |old(shadow)|+1
    ensures   shadow    == old(shadow) + [x]; // new tail
    ensures Valid()
    {
        if n==buf.Length
        {
            var b:= new char[buf.Length];          // temporary
            if m==0 { b:= new char[2*buf.Length]; }// double size
            forall (i | 0<=i<n-m) { b[i]:= buf[m+i]; } // copy m..n to 0..n-m
            buf, m, n:= b, 0, n-m;                     // copy b to buf, reset m,n
        }
        buf[n], n:= x, n+1;         // now we definitely have room
        shadow:= shadow + [x];      // same as previous slide: concat 'x'
    }   

    method Pop() returns(x: char) modifies this, this`n
    requires Valid()
    requires  shadow != [] 
    // code
    ensures   buf    == old(buf)                  // buf name does not change 
    ensures   x      == old(buf[n-1])             // element n-1 is returned
    ensures   n      == old(n-1)                  // n moves down
    // shadow
    ensures |shadow| == |old(shadow)|-1           // popped an elem
    ensures   x      == old(shadow[|shadow|-1])   // last element
    ensures shadow   == old(shadow[..|shadow|-1]) // chop off tail
    ensures Valid()                               // check okay at end
    {
        x, n:= buf[n-1], n-1;                     // get tail, decr n
        shadow:= shadow[..|shadow|-1];            // chop tail off shadow
    }

    //if second-last element is larger than top element, swap
    //if less than 2 elements do nothing
    //specify changes it makes to class in pre + post conds.
    //work w/ shadow
    method TopSort() 
    modifies this, this.buf
    requires Valid()
    ensures |shadow| == |old(shadow)|
    ensures buf.Length == old(buf.Length)
    ensures n == old(n)
    ensures m == old(m)
    ensures buf == old(buf) // ensure pointer to buf doesn't change
    //ensures |shadow| <=1 ==> shadow == old(shadow)
    //ensures |shadow| >=2 && old(shadow[|shadow|-2]) > old(shadow[|shadow|-1]) ==> shadow != old(shadow)
    ensures multiset(buf[m..n]) == multiset(old(buf[m..n]))
    ensures multiset(shadow) == multiset(old(shadow))
    ensures Valid()

    // buf doesn't change so top elements are in order
    ensures n-m >= 2 && (buf[m..n] == old(buf[m..n])) ==> (buf[n-2]) <= (buf[n-1])
    ensures n-m >= 2 && shadow[0..|shadow|] == old(shadow[0..|shadow|]) ==> shadow[|shadow|-2] <= shadow[|shadow|-1]

    // buf hasnt't changed because not enough elements in the stack
    ensures 0<=n<=1 ==> buf[m..n] == old(buf[m..n])
    ensures 0<=|shadow|<=1 ==> shadow[0..|shadow|] == old(shadow[0..|shadow|])
    
    // buf changed so top 2 have swapped and n-2 ele < n-1 ele
    ensures buf[m..n] != old(buf[m..n]) ==> (n-m) >= 2 && (buf[n-2] == old(buf[n-1])) && (buf[n-1] == old(buf[n-2])) && (buf[n-2] < buf[n-1])
    ensures shadow[0..|shadow|] != old(shadow[0..|shadow|]) ==> |shadow| >= 2 && (shadow[|shadow|-2] == old(shadow[|shadow|-1])) && (shadow[|shadow|-1] == old(shadow[|shadow|-2])) && (shadow[|shadow|-2] < shadow[|shadow|-1])
    {   
        // if 2 elements in stack and n-2 > n-1, swap
        if((n-m) >= 2 && (buf[n-2] as int) > (buf[n-1] as int)) {
            var x: char := buf[n-1];
            buf[n-1] := buf[n-2];
            buf[n-2] := x;
            shadow := shadow[|shadow|-1:= shadow[|shadow|-2]][|shadow|-2:= shadow[|shadow|-1]];
        }
    }


} // end of Quack class

/*********************************************************************************/

method Checker()
{
    var p:char, e:bool;
    var q:= new Quack(6);

    q.Push('3');
    q.Push('2');
    q.Push('1');
    q.TopSort();
    p:= q.Pop();    assert p=='2';
    q.TopSort();
    p:= q.Pop();    assert p=='3';
    p:= q.Pop();    assert p=='1';
    e := q.Empty(); assert e;
    q.TopSort();
    e := q.Empty(); assert e;
}