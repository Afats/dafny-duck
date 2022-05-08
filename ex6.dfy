// program verifies in quack + takes ages to do so
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