restart
 == the following is a function
== it takes in two polynomials f,g as input 
== it returns their s-polynomial

Spoly = (f,g) ->
	( gamma := lcm( leadMonomial f, leadMonomial g);
	  s := (1/leadCoefficient f)*lift(gamma/ leadMonomial f ,R)*f-(1/leadCoefficient g)* lift(gamma/ leadMonomial g ,R)*g;
	  return s)

== the following is a function
== it takes in a polynomials f and a list L as input 
== it returns the remainder of the determinate division of f w.r.t the ordered list L

remainderDivisionAlg =(f, L) ->
	( t:= #L; 
	  r:=0; for i to t-1 do a_i=0;
	  lt := apply(L, g-> leadTerm g);
	 while f != 0 do (
				leadf := leadTerm f;
	  			divleads :=select(lt, m-> leadf %m == 0);
				if divleads != {} then ( 
						i:= position(lt, m-> leadf %m == 0) ;
						m := lt_i;
						a_i = a_i +leadf // m;
						f = f-  (leadf // m)*L_i;
						)
				else ( r = r+leadf ;
					f = f - leadf ;
					);
				);
	return r
	)


== in the following example we consider the ring QQ[x,y] with the GrRevLex order
== we let I=(f,g) where f=x^3-2*x*y and g=x^2*y-2*y^2+x
== we want to apply Buchberger's algorithm to find a GB for I

R = QQ[x,y];
f = x^3-2*x*y; 
g = x^2*y-2*y^2+x;
I=ideal(f,g);

== Iteration 1 in Buchberger's algorithm

G'={f,g}; G={f,g};G0={f,g};
s=Spoly(G'_0,G'_1)
remainderDivisionAlg(s,G')
if remainderDivisionAlg(s,G') != 0 then  G=append(G,remainderDivisionAlg(s,G'));
G
G'
G==G'

G1=G;

== Iteration 2 in Buchberger's algorithm

G'=G;
#G'
s1=Spoly(G'_0,G'_1)
remainderDivisionAlg(s1,G')
if remainderDivisionAlg(s1,G') != 0 then  G=append(G,remainderDivisionAlg(s1,G'));
s2=Spoly(G'_0,G'_2)
remainderDivisionAlg(s2,G')
if remainderDivisionAlg(s2,G') != 0 then  G=append(G,remainderDivisionAlg(s2,G'));
s3=Spoly(G'_1,G'_2)
remainderDivisionAlg(s3,G')
if remainderDivisionAlg(s3,G') != 0 then  G=append(G,remainderDivisionAlg(s3,G'));
G
G=unique G;
G==G'

G2=G;

== Iteration 3 in Buchberger's algorithm

G'=G;
#G'
s1=Spoly(G'_0,G'_1)
remainderDivisionAlg(s1,G')
if remainderDivisionAlg(s1,G') != 0 then  G=append(G,remainderDivisionAlg(s1,G'));
G
G'
s2=Spoly(G'_0,G'_2)
remainderDivisionAlg(s2,G')
if remainderDivisionAlg(s2,G') != 0 then  G=append(G,remainderDivisionAlg(s2,G'));
s3=Spoly(G'_0,G'_3)
remainderDivisionAlg(s3,G')
if remainderDivisionAlg(s3,G') != 0 then  G=append(G,remainderDivisionAlg(s3,G'));
s4=Spoly(G'_0,G'_4)
remainderDivisionAlg(s4,G')
if remainderDivisionAlg(s4,G') != 0 then  G=append(G,remainderDivisionAlg(s4,G'));
s5=Spoly(G'_1,G'_2)
remainderDivisionAlg(s5,G')
if remainderDivisionAlg(s5,G') != 0 then  G=append(G,remainderDivisionAlg(s5,G'));
s6=Spoly(G'_1,G'_3)
remainderDivisionAlg(s6,G')
if remainderDivisionAlg(s6,G') != 0 then  G=append(G,remainderDivisionAlg(s6,G'));
s7=Spoly(G'_1,G'_4)
remainderDivisionAlg(s7,G')
if remainderDivisionAlg(s7,G') != 0 then  G=append(G,remainderDivisionAlg(s7,G'));
s8=Spoly(G'_2,G'_3)
remainderDivisionAlg(s8,G')
if remainderDivisionAlg(s8,G') != 0 then  G=append(G,remainderDivisionAlg(s8,G'));
s9=Spoly(G'_2,G'_4)
remainderDivisionAlg(s9,G')
if remainderDivisionAlg(s9,G') != 0 then  G=append(G,remainderDivisionAlg(s9,G'));
s10=Spoly(G'_3,G'_4)
remainderDivisionAlg(s10,G')
if remainderDivisionAlg(s10,G') != 0 then  G=append(G,remainderDivisionAlg(s10,G'));

G=unique G;
G==G'
G3=G

== a faster way to do the computation of the 10 remainders above
for i to #G'-1 do (
	for j from i+1 to #G'-1 do (
		if remainderDivisionAlg(Spoly(G'_i,G'_j),G') != 0 then  G=append(G,remainderDivisionAlg(Spoly(G'_i,G'_j),G'))
		)
)

G=unique G;
G==G'
G3=G

G0
G1
G2
G3

apply( G,leadTerm)
LTI = ideal apply( G,leadTerm)
gens LTI, mingens LTI

transpose matrix {G}, transpose gens gb I

== another example
restart
R=QQ[x,y,z,u,v];
I = ideal(u^5-v^5, v^5-x^5, x^5-y^5, y^5-z^5, u^4*v+v^4*x+x^4*y+y^4*z+z^4*u);
gbTrace=3;
gb I;
viewHelp "gbTrace";
transpose mingens monomialIdeal I

== exercise: determinantal ideals
restart
R=QQ[a..z];
M=genericMatrix(R,3,4)

== compute the GB of ideals of minors of size r
== the code below is an example for r=3 (so, maximal minors)
== try other r's and other size matrices

== CAN YOU COME UP WITH A CONJECTURE ON WHAT THE GB IS?

r=3
I=minors(r,M)
transpose gens gb I
  