==Problem 1 in Computer Worksheet 4 ==
== sample code for part a; change it to work for n instead of 3 then put it inside a for loop ==

R=QQ[x_1..x_3];
u=product gens R;
I=ideal borel matrix {{u}}
# flatten entries gens I

==Problem 2 in Computer Worksheet 4 ==

== code for part d ==
restart
R=QQ[x,y,Degrees=>{{1,0},{0,1}},Heft=>{1,1}];
I=monomialIdeal(y^5, x*y^4, x^2*y^2, x^3*y);
HS= hilbertSeries I;
use degreesRing R;
substitute(HS,{T_0=>x,T_1=>y})

== code for part f ==
(res I).dd


==Problem 3 in Computer Worksheet 4 ==

== code for part c ==
restart
R=QQ[x,y,z,Degrees=>{{1,0,0},{0,1,0},{0,0,1}},Heft=>{1,1,1}];
I=ideal(x^3*y^2*z,x*y^3*z^2,x^2*y*z^3,x^4,y^4,z^4);
HS= hilbertSeries I;
use degreesRing R;
substitute(HS,{T_0=>x,T_1=>y,T_2=>z})
numerator oo

== code for part d ==
(res I).dd

== code for part e (polarization) ===
x=symbol x; y=symbol y; z=symbol z;
S = ZZ[x_1..x_4, y_1..y_4, z_1..z_4];
Ipol=monomialIdeal(x_1*x_2*x_3*y_1*y_2*z_1,x_1*y_1*y_2*y_3*z_1*z_2,
x_1*x_2*y_1*z_1*z_2*z_3,x_1*x_2*x_3*x_4,y_1*y_2*y_3*y_4,z_1*z_2*z_3*z_4)
(res Ipol).dd
(res I).dd