2+2
A=107*431
25!
B=binomial(5,4)
factor 32004
A/B
A//B
A%B

== Most Macaulay2 applications involve polynomial rings over fields and their quotient rings. Fields can be made in various ways:

ZZ/101
QQ
GF 2^5
k = toField (QQ[i]/(i^2+1))

== After making k we can compute in it:
 1/i
 
== We have complex numbers built into M2 
 
 ii
 ii^2

==Computation is often fastest and needs least memory when performed over finite prime fields of the form ℤ/p. Fortunately, when the characteristic p is not too small, qualitative questions often have similar answers over ℤ/p and over ℚ, so we mostly use the former. In Macaulay2 the prime p can range up to 32749.

== We make a polynomial ring in 5 variables over ℤ/101:

kk=ZZ/101
R=kk[x_1..x_5]
char R

== Here are some other ways:

S=kk[a,b,c,d,e]
S=kk[a..e]

== One can do arithmetic on polynomials:

(3*a^2+1)^5

== We make an ideal in S:

 I=ideal(a^3-b^3, a+b+c+d+e)

==Using this ideal, we can make a factor ring:

A=S/I
use S

== Algebraic operations on ideals are available:

 I^2
 I*I
 I+ideal(a^2)

==In case you forget any of these things, help is available! The most useful way to get it is often to type something like:

viewHelp ideal

== Then a browser window will pop up that contains documentation about the function ideal that we’ve been using; links on that page allow one to explore all of the Macaulay2 documentation.

== On the other hand, we might have wanted information about the class of all ideals. Not too surprisingly, this class is called Ideal. We could get information about what functions create or use ideals by typing:

viewHelp Ideal

==To see the names of classes, you can begin by looking at the output of commands; the second line output (the one introduced by a colon) often contains the name of the class of the result.


== THE AFFINE TWISTED CUBIC EXAMPLE ==

==define two polynomial rings and a map between these two rings
restart
k=ZZ/101;
R=k[z,y,x,MonomialOrder=>Lex];
S=k[t];
f=map(S,R,{t^3,t^2,t})
I=ker f
(y^2-x*z)%(ideal(y-x^2,z-x^3))
(x*y-z)%(ideal(y-x^2,z-x^3))
I==ideal(y-x^2,z-x^3)
== a word of warning: mingens should only be trusted for homogeneous ideals
mingens I
P=random(10,R)
P%(ideal(y-x^2,z-x^3))

R=k[z,y,x,Degrees=>{3,2,1},MonomialOrder=>Lex];
degree z
S=k[t];
f=map(S,R,{t^3,t^2,t})
I=ker f
mingens I
