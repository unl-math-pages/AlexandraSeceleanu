-- This M2 file accompanies the paper "A Tight Bound on the Projective 
-- Dimension of Four Quadrics" by Huneke, Mantero, McCullough and Seceleanu
-- Here we provide details for the lemmas in the appendix.
-- In every case, x,y,z represent independent linear forms, i.e. variables.
-- We wish to show that each ideal remains unmixed or even (x,y,z)-primary.
-- By the Buchsbaum-Eisenbud exactness criterion, we must show that the i-th
-- ideal of minors of the expected rank r_i has height at least i for 
-- i = 1, 2, 3 and has height i+1 for i > 3.  To do this we exhibit a regular
-- sequence of the appropriate length or an explicit ideal of the appropriate
-- height in each ideal of minors.
-- (Note:  "x % I == 0" returns true if x is in I and false otherwise.
--  When this technique is too computationally expensive, we construct
--  the appropriate minors by hand.  F.dd_i^L_M returns the submatrix of
--  F.dd_i with rows indexed by the entries of the list L and columns
--  indexed by the entries of the list M.)

-- Lemma A.1
restart
S = QQ[A,B,C,x,y,z]
L = ideal(x^2,y^2,z^2,x*y*z,C*x*y+B*x*z+A*y*z)
F = res L
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(4,F.dd_2) == 0, y^6 % minors(4,F.dd_2) == 0
x^5 % minors(5,F.dd_3) == 0, y^5 % minors(5,F.dd_3) == 0, z^5 % minors(5,F.dd_3) == 0

ass J
degree J

-- Lemma A.2
restart
S = QQ[a,b,c,d,e,f,x,y,z]
J = (ideal(x,y,z))^2 + ideal(a*x+b*y+c*z,d*x+e*y+f*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
-- We construct the regular sequences in I_7(dd_2) and I_7(dd_3) directly
determinant F.dd_2^{0,1,3,4,5,6,7}_{0,1,4,5,8,10,12}
determinant F.dd_2_{2,3,4,5,9,11,13}^{0,1,2,3,5,6,7}

determinant F.dd_3_{2,3,4,5,6,7,8}^{0,1,2,3,4,5,10}
determinant F.dd_3_{0,1,2,3,6,7,8}^{2,3,6,7,9,11,13}
determinant F.dd_3_{0,1,4,5,6,7,8}^{0,1,6,7,8,9,12}

x^2 % minors(2,F.dd_4) == 0, y^2 % minors(2,F.dd_4) == 0, z^2 % minors(2,F.dd_4) == 0
a*e-b*d % minors(2,F.dd_4) == 0, a*f-c*d % minors(2,F.dd_4) == 0, b*f-c*e % minors(2,F.dd_4) == 0

ass J
degree J

-- Lemma A.3
restart
S = QQ[a,b,c,x,y,z]
J = (ideal(x,y,z))^2+ideal(b*x-a*y,c*x-a*z,c*y-b*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
-- check by hand
determinant F.dd_2_{9,10,11,12,13,15,16,17}^{0,1,2,3,4,5,6,7}
determinant F.dd_2_{1,2,4,6,8,11,14,16}^{0,1,3,4,5,6,7,8}

determinant F.dd_3_{5,6,7,8,9,10,11,12,13,14}^{0,1,2,3,4,5,6,7,8,14}
determinant F.dd_3_{1,2,3,4,8,9,11,12,13,14}^{0,1,2,5,9,10,11,12,13,16}
determinant F.dd_3_{0,2,3,4,6,7,10,11,13,14}^{0,3,4,7,9,10,12,13,15,17}

x^5 % minors(5,F.dd_4) == 0, y^5 % minors(5,F.dd_4) == 0, z^5 % minors(5,F.dd_4) == 0, a^5 % minors(5,F.dd_4) == 0, b^5 % minors(5,F.dd_4) == 0, c^5 % minors(5,F.dd_4) == 0

minors(1,F.dd_5)

ass J
degree J

-- Lemma A.4
restart
S = QQ[a,b,c,x,y,z] 
J = (ideal(x,y,z))^2+ideal(a*x+b*y+c*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^6 % minors(6,F.dd_2) == 0
x^5 % minors(5,F.dd_3) == 0, y^5 % minors(5,F.dd_3) == 0, z^5 % minors(5,F.dd_3) == 0
minors(1,F.dd_4)
ass J
degree J

-- Lemma A.5
restart
S = QQ[a,x,y,z]
J = ideal(x,y^2,y*z,z^3,a*y+z^2)
F = res J
F.dd
x % minors(1,F.dd_1) == 0
x^3 % minors(3,F.dd_2) == 0, y^4 % minors(3,F.dd_2) == 0
x^2 % minors(2,F.dd_3) == 0, y^2 % minors(2,F.dd_3) == 0, z^2+a*y % minors(2,F.dd_3) == 0

ass J
degree J

-- Lemma A.6
restart
S = QQ[a,b,c,d,x,y,z]
J = ideal(x^2,x*y,x*z,y^2,y*z,a*x+b*y+z^2,c*x+d*y)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^6 % minors(6,F.dd_2) == 0
x^5 % minors(5,F.dd_3) == 0, y^5 % minors(5,F.dd_3) == 0, (b*y*z^3 + z^5) % minors(5,F.dd_3) == 0
minors(1,F.dd_4)

L = ideal(x^2,x*y,y^2,a*x+b*y+z^2,c*x*z-d*y*z)
G = res L
G.dd
x^2 % minors(1,G.dd_1) == 0
x^5 % minors(4,G.dd_2) == 0, y^5 % minors(4,G.dd_2) == 0
x^4 % minors(4,G.dd_3) == 0, y^4 % minors(4,G.dd_3) == 0, z^6 % minors(4,G.dd_3) == 0
minors(1,G.dd_4)

ass J
degree J

-- Lemma A.7
restart
S = QQ[a,b,x,y,z]
J = ideal(x,y^3,y^2*z,y*z^2,z^3,a*y+b*z)
F = res J
F.dd
x % minors(1,F.dd_1) == 0
x^5 % minors(5,F.dd_2) == 0, y^8 % minors(5,F.dd_2) == 0
x^6 % minors(6,F.dd_3) == 0, y^7 % minors(6,F.dd_3) == 0, z^7 % minors(6,F.dd_3) == 0
x^2 % minors(2,F.dd_4) == 0, y^2 % minors(2,F.dd_4) == 0, z^2 % minors(2,F.dd_4) == 0, a^2 % minors(2,F.dd_2)==0, b^2 % minors(2,F.dd_2) == 0
ass J
degree J


-- Lemma A.8
restart
S = QQ[a,b,c,d,x,y,z]
J = ideal(x^2,x*y,x*z,y*z^2,z^3,a*x+b*y+c*z,d*x+y^2)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^8 % minors(6,F.dd_2) == 0
x^6 % minors(6,F.dd_3) == 0, y^8 % minors(6,F.dd_3) == 0, z^8 % minors(6,F.dd_3) == 0
x^2 % minors(2,F.dd_4) == 0, y^2 % minors(2,F.dd_4) == 0, z^2 % minors(2,F.dd_4) == 0, c^2 % minors(2,F.dd_4)==0, (b^2*d-a*b*y) % minors(2,F.dd_4) == 0
ass J
degree J

-- Lemma A.9
restart
S = QQ[a,b,c,d,x,y,z]
J = ideal(x^2,x*y,x*z,y^3,z^3,a*x+b*y+c*z,d*x+y*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^9 % minors(6,F.dd_2) == 0
x^6 % minors(6,F.dd_3) == 0, y^9 % minors(6,F.dd_3) == 0, z^9 % minors(6,F.dd_3) == 0
x^2 % minors(2,F.dd_4) == 0, y^2 % minors(2,F.dd_4) == 0, z^2 % minors(2,F.dd_4) == 0, b*c % minors(2,F.dd_4)==0, b^2*d % minors(2,F.dd_4) == 0, c^2*d % minors(2,F.dd_4) == 0
ass J
degree J

-- Lemma A.10
restart
S = QQ[a,b,c,x,y,z]
J = ideal(x^2,x*y,x*z,z^3,c*x+y^2,b*x-y*z,a*x+b*y+c*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^6 % minors(6,F.dd_2) == 0
x^5 % minors(5,F.dd_3) == 0, y^5 % minors(5,F.dd_3) == 0, z^8 % minors(5,F.dd_3) == 0
minors(1,F.dd_4)
ass J
degree J

-- Lemma A.11
restart
S = QQ[a,b,c,d,e,f,x,y,z]
J = (ideal(x,y,z))^3+ideal(a*x+b*y+c*z,d*x+e*y+f*z)
F = res J
F.dd
x^3 % minors(1,F.dd_1) == 0

determinant F.dd_2^{0,1,3,4,5,6,7,8,9,10,11}_{0,1,5,8,9,12,16,18,22,24,26}
determinant F.dd_2^{0,1,2,3,4,6,7,8,9,10,11}_{5,6,7,8,9,15,17,19,23,25,27}

determinant F.dd_3^{2,3,4,6,7,10,11,13,14,15,17,19,20,21,23,25,27}_{0,2,3,4,5,7,8,10,12,13,16,17,18,19,22,23,24}
determinant F.dd_3^{0,1,2,3,4,10,11,12,13,14,15,17,20,21,22,23,26}_{1,2,3,4,5,9,11,13,14,15,16,17,20,21,22,23,24}
determinant F.dd_3^{0,1,2,3,4,5,6,7,8,9,10,11,13,14,16,18,24}_{6,7,8,9,11,13,14,15,16,17,18,19,20,21,22,23,24}

determinant F.dd_4^{1,6,9,11,14,15,20,21}_{0,1,3,4,5,6,7,8}
determinant F.dd_4^{0,6,7,8,9,11,18,19}_{0,2,3,4,5,6,7,8}
determinant F.dd_4^{0,1,2,3,4,5,10,12}_{1,2,3,4,5,6,7,8}

factor determinant F.dd_4^{2,7,9,13,16,17,22,23}_{0,1,2,4,5,6,7,8}
factor determinant F.dd_4^{3,8,11,13,16,17,22,23}_{0,1,2,3,5,6,7,8}
factor determinant F.dd_4^{5,11,15,17,13,16,22,23}_{0,1,2,5,3,4,7,8}
factor determinant F.dd_4^{4,9,14,17,13,16,22,23}_{0,1,2,6,3,4,7,8}

-- By symmetry, we have (a^4,b^4,d^4,e^4)(ae-bd)^2 + (a^4,c^4,d^4,f^4)(af-cd)^2+(b^4,c^4,e^4,f^4)(bf-cd)^2
-- in I_8(d_4).  The associated primes of this ideal are (a,b,c,d,e,f) and 
-- (ae-bd, af-cd, bf-ce).  Hence, under the assumptions of the lemma,
-- ht(I_8(d_4)) is at least 5, as desired.
minors(1,F.dd_5)

ass J
degree J

-- Lemma A.12
restart
S = QQ[a,b,x,y,z]
J = (ideal(x,y,z))^3 + ideal(a*x+b*y,a*y+b*z,x*z-y^2)
F = res J
F.dd

x^3 % minors(1,F.dd_1) == 0

determinant F.dd_2^{0,1,2,4,5,6,7,8,9}_{2,3,4,5,7,10,13,16,18}
determinant F.dd_2^{0,1,2,3,4,5,6,7,8}_{7,9,12,13,14,15,17,18,19}

determinant F.dd_3^{0,1,6,8,9,11,12,14,15,17,19}_{0,1,2,4,5,7,8,10,11,13,14}
determinant F.dd_3^{2,3,6,7,8,9,12,13,14,15,18}_{0,1,3,5,6,7,9,11,12,13,14}
determinant F.dd_3^{0,2,3,4,5,6,8,10,12,13,16}_{1,3,5,6,7,9,10,11,12,13,14}

x^4 % minors(4,F.dd_4) == 0, y^4 % minors(4,F.dd_4) == 0, z^4 % minors(4,F.dd_4) == 0, a^4 % minors(4,F.dd_4) == 0, b^4 % minors(4,F.dd_4) == 0

ass J
degree J

-- Lemma A.13
restart
S = QQ[a,b,x,y,z]
J = ideal(x^2,x*y,x*z,y^2,y*z,z^3,a*x+b*y+z^2)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^5 % minors(5,F.dd_2) == 0, y^6 % minors(5,F.dd_2) == 0
x^3 % minors(3,F.dd_3) == 0, y^3 % minors(3,F.dd_3) == 0, z^4 % minors(3,F.dd_3) == 0
ass J
degree J

-- Lemma A.14
restart
S = QQ[a,b,c,x,y,z]
J = ideal(x^2,x*y,x*z,y^3,y^2*z,y*z^2,z^3,a*x+b*y+c*z)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^7 % minors(7,F.dd_2) == 0, y^10 % minors(7,F.dd_2) == 0
determinant F.dd_3^{3,4,6,8,9,11,13}_{0,1,2,4,5,7,8}
determinant F.dd_3^{0,2,6,7,9,10,12}_{0,1,3,4,6,7,8}
determinant F.dd_3^{1,4,5,0,6,7,10}_{0,3,4,5,6,7,8}
x^2 % minors(2,F.dd_4) == 0, y^2 % minors(2,F.dd_4) == 0, z^2 % minors(2,F.dd_4) == 0, b^2 % minors(2,F.dd_4) == 0, c^2 % minors(2,F.dd_4) == 0
ass J
degree J

-- Lemma A.15
restart
S = QQ[a,b,c,d,x,y,z]
J = ideal(x^2,x*y,y^2,a*x+b*y+z^2,c*x+d*y)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^5 % minors(4,F.dd_2) == 0, y^5 % minors(4,F.dd_2) == 0
x^4 % minors(4,F.dd_3) == 0, y^4 % minors(4,F.dd_3) == 0, z^8 % minors(4,F.dd_3) == 0
minors(1,F.dd_4)
ass J
degree J

-- Lemma A.16
restart
S = QQ[a,b,c,d,e,f,x,y,z]
J = ideal(x^2,x*y,y^2,a*x+b*y,c*x+d*y,a*d-b*c+e*x+f*y)
F = res J
F.dd
x^2 % minors(1,F.dd_1) == 0
x^5 % minors(5,F.dd_2) == 0, y^5 % minors(5,F.dd_2) == 0
x^3 % minors(3,F.dd_3) == 0, y^3 % minors(3,F.dd_3) == 0, (a*(a*d-b*c)-b*e*y+a*f*y) % minors(3,F.dd_3) == 0, (d*(a*d-b*c)+d*e*x-c*f*x)% minors(3,F.dd_3) == 0, (c*(a*d-b*c)-d*e*y+c*f*y) % minors(3,F.dd_3) == 0, (b*(a*d-b*c)+b*e*x-a*f*x) % minors(3,F.dd_3) == 0
ass J
degree J

-- Lemma A.17
restart
S = QQ[a,b,c,u,v,x,y,z]
J = ideal(x,y,z)*ideal(u,v) + ideal(a*x+b*y+c*z)
F = res J
F.dd
x*u % minors(1,F.dd_1) == 0
v^2*z^4 % minors(6,F.dd_2) == 0, u^2*x^4 % minors(6,F.dd_2) == 0

-- Note: Here we show that (x^4, y^4, z^4)(u,v) + (x^3, y^3, z^3)(ax+by+cz)
-- is a height 3 subideal of I_5(dd_3)
determinant F.dd_3^{0,2,3,4,5}_{0,2,3,4,5}
determinant F.dd_3^{1,2,3,4,5}_{0,2,3,4,5}
factor determinant F.dd_3^{2,3,4,5,6}_{0,2,3,4,5}
determinant F.dd_3^{0,3,6,9,10}_{0,1,2,4,5}
determinant F.dd_3^{1,3,6,9,10}_{0,1,2,4,5}
factor determinant F.dd_3^{2,3,6,9,10}_{0,1,2,4,5}
determinant F.dd_3^{0,2,6,7,8}_{0,1,3,4,5}
determinant F.dd_3^{1,2,6,7,8}_{0,1,3,4,5}
factor determinant F.dd_3^{2,3,6,7,8}_{0,1,3,4,5}

minors(1,F.dd_4)

ass J
degree J

--Lemma A.18
restart
S = QQ[a,b,c,d,w,x,y,z]
J = ideal(x^2,x*y,x*z,y^2,y*z,a*x+b*y+w*z,c*x+d*y)
F = res J
ass J

x^2 % minors(1,F.dd_1) == 0
x^6 % minors(6,F.dd_2) == 0, y^6 % minors(6,F.dd_2) == 0
x^5 % minors(5,F.dd_3) == 0, y^5 % minors(5,F.dd_3) == 0, z^4*w + b*y*z^3 % minors(5,F.dd_3) == 0
minors(1,F.dd_4)

ass J
degree J
