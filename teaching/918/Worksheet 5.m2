== Computer Worksheet 5 code ====

== Problem 1 ==

restart
R=QQ[x_1..x_4,MonomialOrder=>{Position=>Up,GRevLex=>4}]
I=ideal(x_1*x_2*x_4^4, x_1*x_2*x_3*x_4^2, x_1*x_3^6,x_1*x_2*x_3^2,  x_2^6, 
 x_1*x_2^2,  x_1^2)
monI = monomialIdeal(x_1*x_2*x_4^4,x_1*x_2*x_3*x_4^2,x_1*x_3^6,x_1*x_2*x_3^2,x_2^6, x_1*x_2^2,x_1^2)
I == monI
isBorel monomialIdeal I
r = res I
r.dd
betti r
G = gens gb ker (r.dd_1)
leads = for i to (numcols G -1) list leadTerm G_i
M = image matrix leads
res M

=== Problem 2 ===

restart
gin = I -> (
	   R:= ring I;
	   n := # gens R;
	   g:= random(R^1,R^{n:-1}); 
	   F := map(R,R,g);
	   genericI := F I;-- or:  genericI := substitute(I,g);
	   generic = monomialIdeal genericI;
	   good := isBorel generic; 
	   if not good then stderr << "--warning: potential generic initial ideal is not Borel-fixed" << endl;
	   return generic      
 );

loadPackage "GenericInitialIdeals"
gin(I, MonomialOrder => Lex)
gin(I, MonomialOrder => GRevLex)



=== Problem 3 ===

restart
R=QQ[x,y]
 I= ideal (x^2,x*y,y^3)
loadPackage "Posets"
L= lcmLattice I
texPoset(L,SuppressLabels=> false)
betti res I
(res I).dd
O=orderComplex openInterval(L, 1_S, x^2*y)
for i to 5 list prune HH_i O
