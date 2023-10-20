--(4,3,5)

R=ZZ/101[x,y,z,u]
l=random(R^{1},R^1)
I=ideal apply(flatten entries l,i->i^3)+ideal(x^3,y^3,z^3,u^3)
betti res( I)
a=random(R^{1},R^1)
b=(flatten entries a)_0
S=R/ideal(b)
J=(map(S,R))I
betti res J
for i to 5 list hilbertFunction(i,I)
-- {1, 4, 10, 15, 15, 6}
-- h^0(S(I)|L)_4 = 1 = h^1(S(I)|L)_4 so we have 0-> 1 -> 15 -> 15 -> 1 (???) so WLP fails (twin peaks)
-- here (P^3) h^2(S(I))=h^0(S(I)) and hence h^2(S(I)_3 = h^0(S(I))_5 = 1 ???
-- NOTE: special systems influence injectivity in P^3 (b/c S(I)|_L lives on P^2)


            0 1  2  3 4
o4 = total: 1 5 17 20 7
         0: 1 .  .  . .
         1: . .  .  . .
         2: . 5  .  . .
         3: . .  .  . .
         4: . . 16 10 1
         5: . .  1 10 6


             0 1 2 3
o14 = total: 1 5 7 3
          0: 1 . . .
          1: . . . .
          2: . 5 1 .
          3: . . 6 2
          4: . . . 1

-- (5,3,9)

R=ZZ/101[x,y,z,u,v]
l=random(R^{1},R^4)
I=ideal apply(flatten entries l,i->i^3)+ideal(x^3,y^3,z^3,u^3,v^3)
betti res( I)
a=random(R^{1},R^1)
b=(flatten entries a)_0
S=R/ideal(b)
J=(map(S,R))I
betti res J
for i to 5 list hilbertFunction(i,I)
-- {1, 5, 15, 26, 25, 0}
-- h^0(S(I)|L)_4 = 2 so we have 0-> 2 -> 26 -> 25 -> 1 (???) so WLP fails 
-- here (P^4) h^2(S(I))=h^1(S(I)) and since S(I) is special h^2(S(I))_3=h^1(S(I)_4 = 1 ???
-- NOTE: special systems influence surjectivity in P^4 

           0 1  2   3  4  5
o4 = total: 1 9 69 135 99 25
         0: 1 .  .   .  .  .
         1: . .  .   .  .  .
         2: . 9  .   .  .  .
         3: . .  9   .  .  .
         4: . . 60 135 99 25

            0 1  2  3 4
o9 = total: 1 9 28 28 8
         0: 1 .  .  . .
         1: . .  .  . .
         2: . 9  2  . .
         3: . . 26 28 7
         4: . .  .  . 1


-- (6,3,14)

R=ZZ/101[x,y,z,u,v,w]
l=random(R^{1},R^8)
I=ideal apply(flatten entries l,i->i^3)+ideal(x^3,y^3,z^3,u^3,v^3,w^3)
betti res( I)
a=random(R^{1},R^1)
b=(flatten entries a)_0
S=R/ideal(b)
J=(map(S,R))I
betti res J
for i to 5 list hilbertFunction(i,I)
-- {1, 6, 21, 42, 42, 0}
-- h^0(S(I)|L)_4 = 1 so we have 0-> 1 -> 42-> 42 -> 1 hence WLP fails (twin peaks)

            0  1   2   3   4   5  6
o4 = total: 1 14 112 330 399 210 42
         0: 1  .   .   .   .   .  .
         1: .  .   .   .   .   .  .
         2: . 14   .   .   .   .  .
         3: .  .  42   .   .   .  .
         4: .  .  70 330 399 210 42

            0  1  2   3  4  5
o9 = total: 1 14 80 130 80 17
         0: 1  .  .   .  .  .
         1: .  .  .   .  .  .
         2: . 14  1   .  .  .
         3: .  . 79 130 80 16
         4: .  .  .   .  .  1

--(6,2,7)

R=ZZ/101[x,y,z,u,v,w]
l=random(R^{1},R^1)
I=ideal apply(flatten entries l,i->i^2)+ideal(x^2,y^2,z^2,u^2,v^2,w^2)
betti res( I)
a=random(R^{1},R^1)
b=(flatten entries a)_0
S=R/ideal(b)
J=(map(S,R))I
betti res J
for i to 5 list hilbertFunction(i,I)
-- {1, 6, 14, 14, 5, 0}
-- h^0(S(I)|L)_3 = 4 so we have 0-> 4-> 14 -> 14 -> 4 so WLP fails (twin peaks)

             0 1  2  3  4  5 6
o12 = total: 1 7 26 51 52 26 5
          0: 1 .  .  .  .  . .
          1: . 7  .  .  .  . .
          2: . . 26 16  5  . .
          3: . .  . 35 32 10 .
          4: . .  .  . 15 16 5

            0 1  2  3  4 5
o9 = total: 1 7 19 25 16 4
         0: 1 .  .  .  . .
         1: . 7  4  .  . .
         2: . . 15 16  4 .
         3: . .  .  9 12 4

-- function for checking WLP
checkWLP := I-> (
S=ring I;
A=S/I;
n=# gens ring I;
L=(random(S^1,S^n)*(transpose vars S));
t=map(A,S);
f = map(A^1, A^{-1}, t(L));
i=1;
while (not (basis(i,A) == 0)) do(
              	  mat= inducedMap(image super basis(i,target f), image super basis(i,source f), f);
		  newmat = map(A^(numrows mat),A^(numcols mat),mat);
		  mindim = min(# flatten entries super basis(i,target f), # flatten entries super basis(i,source f));
		print(i,rank newmat,mindim);
              	  i=i+1;
			);
)


buildIdeal := (R,nforms,pow)->(
     l=random(R^{1},R^nforms);
     ideal apply(flatten entries l,i->i^pow)
)


-- 8 lin forms to 8th power

-- in P^3

           0 1   2   3  4
o9 = total: 1 8 144 229 92
         0: 1 .   .   .  .
         1: . .   .   .  .
         2: . .   .   .  .
         3: . .   .   .  .
         4: . .   .   .  .
         5: . .   .   .  .
         6: . .   .   .  .
         7: . 8   .   .  .
         8: . .   .   .  .
         9: . .   .   .  .
        10: . .   .   .  .
        11: . .   .   .  .
        12: . .   .   .  .
        13: . . 144 225 84
        14: . .   .   4  8


-- in P^2

             0 1  2  3
o18 = total: 1 8 25 18
          0: 1 .  .  .
          1: . .  .  .
          2: . .  .  .
          3: . .  .  .
          4: . .  .  .
          5: . .  .  .
          6: . .  .  .
          7: . 8  .  .
          8: . .  .  .
          9: . .  2  .
         10: . . 23 18


-- HF      ={1, 4, 10, 20, 35, 56, 84, 120, 157, 188, 206, 204, 175, 112, 8}
-- HFsmall ={  1, 3, 6,  10, 15, 21, 28,  36,  37,   31, 18}


-- m  0 - 9    10         11    12          13       14-inf
--     inj  non-inj  non-inj  non-inj      non-inj    non-inj
--          surj     surj     surj         surj       surj

--D_10=10*E_0-\sum 3*E_i contains DD
--D_11, D_12 etc contain DD=6E_0-\sum 2*E_i -E_8
-- but every one contains DDD=2E_0-E_1-E_2

DD*D_j=6j-17(j-7)=-11j+111 <=-2 iff j>10


in general 

DD*D_j=6j-2(7j-/sum a_i)-3(j-a_8)=-11j+2\sum a_i +a_8<=-2 iff 2\sum a_i+3a_8>10
DDD=E_0-E_1-E_2
DDD*D_j=j-(2j-a_1-a_2)=-j+a_1+a_2

-j+2a
-2j+3a

d=1
j-2(j-t+1)=-j+2t-2<=-2 iff j>=2t

d=2
2j-5(j-t+1)=-3j+5t-5<=-2 iff j>=(5t-3)/3

d=3
3j-8(j-t+1)=-5j+8t-8<=-2 iff j>=(8t-6)/5

d=4
4j -11(j-t+1)=-7j+11t-11<=-2 iff j>=(11t-9)/7

d=5
5j -13(j-t+1)=-9j+14t-14<=-2 iff j>=(14t-12)/9

d=6
6j-15(j-t+1)=-11j+17t-17<=-2 iff j>=(17t-15)/11


min(j)=ceil[(17/11)t-15/11]

here t=8 so we get ceil[111/11]=11

------------------------------------------------------------------

9 points unif mult 8
HF       ={1, 4, 10, 20, 35, 56, 84, 120, 156, 184, 196, 184, 140, 56,}
HF small =  {1, 3, 6,  10, 15, 21, 28,  36,  36,  28,  12}



--==================================================================

pointsonconic:= (n,pow)->(
	ideal apply( flatten for i from 1 to n list flatten entries (vars R* (transpose matrix{{i^1,i^2,i^3}})),j->j^pow)
)

{1, 3, 6, 10, 15, 21, 28, 36, 39, 37, 30, 19, 10, 4, 1, -- 6 lin f on conic ^8, in QQ[x,y,z]
{1, 3, 6, 10, 15, 21, 28, 36, 39, 37, 30, 18, 1} -- 6 lin f gen pos ^8 in QQ[x,y,z]

