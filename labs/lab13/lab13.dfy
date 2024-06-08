method test1a(x: int, y: int) returns (z: int)
{
    assume(x==y);
    z:=x-y;
    assert(z==0);
}

// ne asumam ca x=y, x si y fiind egale, z devine intotdeauna 0, astfel ca se verifica intotdeauna asertiunea


method test1b(x: int)
{
    assume(true);
    var x:=100;
    assert(x==100);
}

// aceasta asumptie nu are legatura cu x, fiind o axioma, x ia valoarea 100, fara nicio pb fiind un nr intreg, iar la final putem spune ca x este 100 oricare ar fi x initial, daca in assert ar fi fost x!=100, atunci testul ar fi picat de fiecare data

method test2a(x: int, y: int)
{
    assume(true);
    var x:=2*y;
    assert(y<=x);
}

// x=1, y=-1 => x=-2, y=-1 => (-1)<=(-2) fals

method test2b(x: int)
{
    assume(0<=x);
    var x:=x-1;
    assert(0<=x);
}

// x=0
// 0<=0  =>  x=-1 =>  0<=-1 fals

method test3a(x: int)
{
    assume(0<=x && x<100 );
    var x:=2*x;
    assert(0<=x);
    assert(x<200);
}

method test3b(x:int)
{
    assume(0<=x);
    assume(x<100);
    var x:=2*x;
    assert(0<=x);
    assert(x<200);
}

method test4a(x: int)
{
    assume(x==400);
    var x:=400;
    assert(x==400);
}


method test4b(x: int, y:int)
{
    assume(y<=65);
    var x:=65;
    assert(y<=x);
}




// stim ca 0<=x<100 => (line 27) 0<1<=x<=101 => 0<=x<=100.

method test1c(x: int)
{
    assume(0<=x);
    assume(x<100);
    var x:=x+1;
    assert(0<=x);
    assert(x<=100);
}








method sum(n:nat) returns (sum: nat)
requires n>=0
ensures sum== n*(n+1)/2
{
    sum:=0;
    var i:=0;
    while i<=n
    invariant 0<=i
    invariant i<=n+1
    invariant sum==i*(i-1)/2
    {
        sum:=sum+i;
        i:=i+1;
    }

}