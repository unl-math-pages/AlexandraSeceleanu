restart
J = (g,M) -> ( -- g >= 2, #M >= 2
     n := #M;
     d := i -> sum(take(M, -(n - i)-1))+1;
     ZZ[t_1..t_g];
     m := last M;  
     ind := (g,M) ->  apply(apply( toList fold((i,j) -> i**j,
	  append(
     apply(drop(M,-1), m -> 
	  set flatten apply(select(terms product(1..g, j -> 
			 sum(m, i -> t_j^i)), i -> 
		    first degree i == m),exponents)),
     set flatten apply(select(terms product(1..g, j -> sum(m+1, i -> t_j^i)), 
	       i -> first degree i == m),exponents)))/deepSplice,toList),i -> transpose matrix i);     
     front := (g,M) ->if #M == 1 then apply(flatten apply(M, m -> flatten apply(select(terms product(1..g, j -> 
			 sum(m, i -> t_j^i)), i -> 
		    first degree i == m), exponents)),i->transpose matrix {i}) else apply(apply( toList fold((i,j) -> i**j,
     	       apply(M, m -> set flatten apply(select(terms product(1..g, j -> 
			 sum(m, i -> t_j^i)), i -> 
		    first degree i == m),
	       exponents)))
     /deepSplice,toList),i -> transpose matrix i);
     middle := (i,g,M) -> (
	  A := mutableMatrix(ZZ,g,2);
	  A_(0,0) = M_(i); --was i+1	    
	  A_(0,1) = d(i+2);
	  {matrix A}|toList(apply (0..g-2, i-> matrix rowSwap(A,i,i+1)))
	  );
     matrixListPre := flatten toList apply(1..n-2, -- change to 0 to n-3
	  i -> flatten apply(front(g,take(M,i)),j -> flatten apply(middle(i,g,M), k -> j|k)));
     matrixList := apply(middle(0,g,M)|matrixListPre, i -> i | map(ZZ^g, ZZ^(n-rank source i), 0));
          k := ZZ/5051;
	  indList := ind(g,M);
     B = k[x_(1,1)..x_(g,n), apply(indList, i -> z_i)];
     ideal(apply(x_(1,1)..x_(g,1), i -> i^(d 1)),sum apply(matrixList,m-> product flatten for i to g-1 list ( for j to n-1 list x_(i+1,j+1)^(m_(i,j))))+sum apply(indList,m-> (product flatten for i to g-1 list ( for j to n-1 list x_(i+1,j+1)^(m_(i,j))))*z_m))
)     

a = J(2,{2,3,2})

b = J(2,{2,2,2,1})
f=map(ZZ/5051[x_(1,1)..x_(2,4)],B)
f b
regularity (f(b))  


---- things below this line are outdated !

-- Start 3:

restart
J = (g,M) -> ( -- g >= 2, #M >= 2
     n := #M;
     d := i -> sum(take(M, -(n - i)-1))+1;
     ZZ[t_1..t_g];
     m := last M;  
     Pre = append(
	  apply(drop(M,-1), m -> set flatten apply(select(terms product(1..g, j -> sum(m, i -> t_j^i)), i -> first degree i == m),exponents)),
	  set flatten apply(select(terms product(1..g, j -> sum(m+1, i -> t_j^i)), i -> first degree i == m),exponents)
	  );
     k := ZZ/5051;
     B = k[x_(1,1)..x_(g,n), apply(
	       apply(
		    apply(toList fold((i,j) -> i**j, 
			      
			      Pre
			      
			      )/splice, toList), i -> transpose matrix i)
	       
	       
	       , i -> z_i)];
     ideal(apply(x_(1,1)..x_(g,1), i -> i^(d 1)))
     );
J(2,{2,2,2,2,2})
Pre
describe B




-- index on z's will be matricies. 

restart 
M = {2,2,3};
g = 3;


# 


viewHelp fold
flatten apply(select(terms( (
     	    
drop(M,-1)		    
PreS = {set {1,2,3},set {4,5},set{3,4,5}}
C = PreS_0
apply(drop(PreS,1), s -> C = C ** s)

drop({2,3,4},0)

flatten apply(select(terms( (1 + t+ t^2+t^3)*(1+s+s^2+s^3)*(1+w+w^2 + w^3)), i -> first degree i == 4), exponents)

(partitions 4)_0_0

viewHelp symbol 

P = apply(#M,
     apply(M, i -> partitions i)



P_2
J(3,{2,3,4,5})     


f 5


ideal(apply(x_(1,1)..x_(g,1), i -> i^(d 1)), f)



     L = prepend(0,L); -- WARNING shifts L -- now indicies match
     f = S -> (if #S == n then sum(0..L_n-1, i -> x_n^i*y_n^(L_n - i - 1)*z_(toSequence append(S,i)))));
-------------------------------------------------------------     	  
     
	  
	  
	  
	  
	  
	  
	  
	  
	  
	  

     
n = 3

J(L)     


S = {1,2,3,2}
f S
B
describe B

     ideal(x_1^d, y_1^d,
	  x_1^(L_1)
	  )
     )

L = {0,3,4,3}
append((3,4),5)
td(1)
J({2,3,4})     
describe B

    - note this is a local variable
     ideal(a^(l+m+n), b^(l+m+n)) + ideal( 
     );
J(5,2)
{(5:1) .. splice(4:4, 5)}

reverse(1..5)
L = {3,4,5,2}


viewHelp



pd = i -> length res i 

Js = (d, m) -> a^(d-1) * b^(d-1) * u^(d-m-1) * v^(d-m-1)

J(5,3)
describe B
socle = (d,m) -> (
     Js := (d, m) -> a^(d-1) * b^(d-1) * u^(d-m-1) * v^(d-m-1);
     I := J(d,m);
     if Js(d,m) % I == 0 then false else max (apply(gens B, i -> i *Js(d,m) % I)) == 0
     );

socle(6,3)
dim B
     
regularity J(7,1)
degree J(7,3)
pd J(5,3)

# gens B


----------------------------------------------------------------------------------

R = ZZ/101[a,b,x_1..x_8,u,v,z,w]
--I = ideal (a^5, b^5, a^3*u^2 + a^2*b*x_(1,1)*u + a^2*b*x_(1,0)*v + a*b^2*x_(2,1)*u + a*b^2 *x_(2,0)*v + b^3*v^2)
I = ideal (a^5, b^5, 
     a^3*u^2 + 
     a^2*b*x_1*u + a^2*b*x_2*v + 
     a^2*b*x_3*w + a^2*b*x_4*z + 
     a*b^2*x_5*w + a*b^2*x_6*z + 
     a*b^2*x_7*u + a*b^2*x_8*v + 
     b^3*v^2)

I = ideal (a^5, b^5, 
     a^3*w^2 + a^3*u^2 + 
     a^2*b*x_1*u + a^2*b*x_2*v + 
     a^2*b*x_3*w + a^2*b*x_4*z + 
     a*b^2*x_5*w + a*b^2*x_6*z + 
     a*b^2*x_7*u + a*b^2*x_8*v + 
     b^3*v^2 + b^3*z^2)
J(5,2)
isHomogeneous I
pd I
dim R






-- original big ideal

J = (d, m) -> (
     k := ZZ/5051;
     B = k[a,b,x_(1,0)..x_(m-1,d-m-1),u,v]; -- note this is a local variable
     ideal(a^d, b^d) + ideal(a^m*u^(d-m) + b^m*v^(d-m) + sum(1..(m-1), i-> a^(m-i)*b^i* sum(0..(d-m-1), j -> u^j*v^(d-m-j-1)*x_(i,j))))
     );
J(11)
# gens B

-------------------------------------------------------------
-- start 1

restart
J = L -> (
     n := #L;
     d := sum(L);
     td := i -> sum(take(L, -(n - i)));
     k := ZZ/5051;
     B := k[x_1..x_n, y_1..y_n,z_(splice(n-1:1,0))..z_(toSequence apply(L, i -> i -1))];
     L = prepend(0,L); -- WARNING shifts L -- now indicies match
     f = S -> (if #S == n then sum(0..L_n-1, i -> x_n^i*y_n^(L_n - i - 1)*z_(toSequence append(S,i)))));
-------------------------------------------------------------     	  

-- start 2

