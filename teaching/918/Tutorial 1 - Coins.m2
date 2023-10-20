== Adapted from "Computations in Algebraic Geometry with Macaulay2" edited by Eisenbud, Grayson,Stillman, Sturmfels
== chapter 1, section 5

restart
A = {{1, 1, 1, 1},
     {1, 5,10,25}}
R = QQ[p,n,d,q, Degrees => transpose A]
degree d
degree q

 ==  four pennies, eight nickels, ten dimes, and three quarters ==
degree(p^4*n^8*d^10*q^3)
== possible ways of having 25 coins for a total vaule of 2 dollars 19c ==
h = basis({25,219}, R)
rank source h
== number of ways can you make change for ten dollars using 100 coins ==
rank source basis({100,1000}, R)

== or the Hilbert function way
hilbertFunction({100,1000}, R)


== among all 182 ways of ex- pressing ten dollars using 100 coins, which one uses ==
== the fewest dimes? using the Conti-Traverso algorithm ==


S = QQ[x, y, d, p, n, q, 
    MonomialOrder => Lex, MonomialSize => 16]
I = ideal( p - x*y, n - x*y^5, d - x*y^10, q - x*y^25)
transpose gens gb I
(x^10 * y^100)%I
(x^100 * y^1000)%I

==or we could do

S' = S/I
x^10 * y^100
x^100 * y^1000

== The integer program is infeasible if and only if the normal form still contains ==
==  the variable x or the variable y. ==
== For instance, you cannot express ten dollars with less than forty coins: ==
x^39 * y^1000

