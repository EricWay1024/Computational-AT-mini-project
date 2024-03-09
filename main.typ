#import "template.typ": *
#show: thmrules
#show: project.with(
  title: "Computational Algebraic Topology",
  subtitle: [A mini-project submitted for the degree of
  
   _MSc Mathematical Sciences_],
  author: "Candidate Number 1079278", 
  date: "Hilary Term, 2024"
)

#pagebreak()

#TODO[reminder: add punctuations to displayed formulae]

= Task 1
Throughout this section, let $K$ be a finite simplicial complex. Write $(K, >=)$ for the poset of simplices in $K$ ordered by face relations, which can also be naturally seen as a category, where each simplex in $K$ is an object and each face relation $tau >= sigma$ is a morphism $tau -> sigma$. 
#definition[
  A *cosheaf over $K$* which takes values in $FF$-vector spaces  is a functor $cC : (K, >=) -> VF$.
  In other words, $cC$ assigns 
  + to each simplex $tau$ of $K$ a finite-dimensional vector space $cC(tau)$ over $RR$, and
  + to each face relation $tau >= sigma$ a linear map $cC(tau >= sigma) : cC(tau) -> cC(sigma)$,
  subject to the following axioms:
  + for every simplex $tau$ in $K$, the map $cC(tau >= tau)$ is the identity on $cC(tau)$, and 
  + for each triple $tau >= sigma >= rho $ in $K$, we have $cC(sigma >= rho) oo cC(tau >= sigma) = cC(tau >= rho)$.
]
Write $FVR$ for the category of finite-dimensional vector spaces over $RR$. In particular, a cosheaf over $K$ which takes values in finite-dimensional real vector spaces is a functor $cD : (K , >=) -> FVR$. 

Now fix a cosheaf $cC : (K, >=) -> VF$ over $K$.

#definition[
  For each dimension $k>=0$, the vector space of *$k$-chains of $K$* with $cC$-coefficients is the product 
  $
    bC_k (K; cC) = product_(dim tau = k) cC(tau).
  $

  For each $k >= 0$, the $k$-th *boundary map* of $K$ with $cC$-coefficients is the linear map 
  $
    diff^cC_k : bC_k (K ; cC) -> bC_(k+1) (K ; cC),
  $
  defined such that for each pair of simplices $tau >= sigma$ with $dim tau = k$ and $dim sigma = k - 1$, the $cC(tau) -> cC(sigma)$ component of $diff^cC_k$ is given by 
  $
    diff^cC_k|_(tau, sigma) = [sigma : tau] dot cC(tau >= sigma),
  $
  where 
  $
    [sigma : tau] := cases(
      +1 quad &sigma = tau_(-i) " for " i "even,",
      -1 quad &sigma = tau_(-i) " for " i "odd,",
      0 quad &"otherwise."
    )
  $
]

#let ct(k, co: cC) = [$bC_#k (K; #co)$]
#let cf(k, co: cC) = [$diff^#co _ #k$]
#let cfa(k, co: cC) = [$->^cf(#k, co: co)$]
#let cft(k, co: cC) = [$ ct(#k, co: co) cfa(#k, co: co)$]

#proposition[
  The sequence $bC_cx (K; cC)$
  $
    ... cfa(k+1) cft(k)  ... cft(1) ct(0) -> 0
  $
   is a chain complex over $FF$. 
]
#proof[
  #TODO[copy the notes..]
]

#definition[
  For each dimension $k >= 0$, the *$k$-th homology group of $K$ with coefficients in $cC$* is defined by 
  $
    bH_cx (K; cC) := Ker(cf(k)) over Im(cf(k+1)).
  $
]

#definition[
  Let $V$ be a $FF$-vector space.
  The *constant* cosheaf $underline(V)_K : (K , >=) -> VF$ is the functor given as follows:  
  $
    underline(V)_K : (K , >=) &-> VF \
    tau &mapsto V \
    (tau >= sigma) &mapsto id_V.
  $
]

= Task 2
Let $cC$ and $cC'$ be two cosheaves over $K$. 

#definition[
  A *morphism of cosheaves* over $K$ is a natural transformation $Phi : cC -> cC'$. In other words, $Phi$ consists of the following data: for each $tau in K$, there is a linear map $Phi_tau : cC(tau) -> cC'(tau)$, such that the following diagram of linear maps commutes for each $tau >= sigma$:
  // https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRAGMBhAChzqYCUIAL6l0mXPkIoyARiq1GLNl27YA5gFs6Q0eOx4CRWeQX1mrRB04ByXv11iQGA1OOl51c8qtc7G7V0FGCh1eCJQADMAJwhNJDIQHAgkE0ULFR4+JgACAD4AXhyAnREnGLikACZqZKQAZi8lS2s7bPyiksco2PjERLrEGvSfEAAFAAssAH1ssp7KxDTBxpGWyZmSkQphIA
#align(center, commutative-diagram(
  node-padding: (70pt, 50pt),
  node((0, 0), [$cC(tau)$]),
  node((1, 0), [$cC(sigma)$]),
  node((0, 1), [$cC'(tau)$]),
  node((1, 1), [$cC'(sigma).$]),
  arr((0, 0), (1, 0), [$cC(tau >= sigma)$]),
  arr((0, 1), (1, 1), [$cC'(tau >= sigma)$]),
  arr((0, 0), (0, 1), [$Phi_tau$]),
  arr((1, 0), (1, 1), [$Phi_sigma$]),
))
]
<morphism-of-cosheaves>

Now fix a morphism $Phi : cC -> cC'$ of cosheaves. 

#proposition[
  $Phi : cC -> cC'$ induces a chain map $bC_cx (K; cC) -> bC_cx (K; cC')$.
]
#proof[
  For each $k>=0$, write $Phi_k : bC_k (K; cC) -> bC_k (K; cC')$ for the linear map whose $cC(tau) -> cC'(tau')$ component is $Phi_tau$ when $tau = tau'$ and is $0$ otherwise, where $tau$ and $tau'$ are simplices in $K$ such that $dim(tau) = dim(tau') = k$. We claim that ${Phi_k}_(k>=0)$ is a chain map $bC_cx (K; cC) -> bC_cx (K; cC')$, i.e., the following diagram commutes:

// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRAGEB9AawAIAKANIBuXgGN2AShABfUuky58hFAEZyVWoxZsu-bgFpVkgSPFTZ8kBmx4CRMqs31mrRBx6nREgOTS5CrbKROpO1C467nqGxl7mfrKaMFAA5vBEoABmAE4QALZIZCA4EEgATOHabiAACgAWWDyWWbkFiOrFpYgAzJWubPWN+kb+Vjn5hdQlSB0R1VBYmZk8AHoSzSDjbRWdSL1a-e4LS6v8vv4UMkA
#align(center, commutative-diagram(
  node-padding: (70pt, 50pt),
  node((0, 0), [$bC_k (K; cC)$]),
  node((0, 1), [$bC_(k-1) (K; cC)$]),
  node((1, 0), [$bC_k (K; cC')$]),
  node((1, 1), [$bC_(k-1) (K; cC').$]),
  arr((0, 0), (1, 0), [$Phi_k$]),
  arr((0, 1), (1, 1), [$Phi_(k-1)$]),
  arr((0, 0), (0, 1), [$diff_k^cC$]),
  arr((1, 0), (1, 1), [$diff_k^(cC')$]),
))

  By linearity and by how we define each $Phi_k$, it suffices to consider an arbitrary pair of simplices $tau >= sigma$ such that $dim tau = k$ and $dim sigma = k - 1$, in which case the above diagram becomes:
  
    // https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRAGMBhAChzqYCUIAL6l0mXPkIoAjOSq1GLNl27YA5gFs6Q0eOx4CRMjIX1mrRB04ByAAS9+usSAwGpROaernlVrvZqWFo6IgowUOrwRKAAZgBOEJpIZCA4EEhyihZsyBradoh2fEwUdqoldgB8ALx2+aF6IAlJSABM1OlIAMw+SpYgecEFRSVlAY5M1XUNznGJyYipXYgd2X4gAAoAFlgA+iUiLi2LWSu96wM7+w1hwkA
#align(center, commutative-diagram(
  node-padding: (100pt, 50pt),
  node((0, 0), [$cC(tau)$]),
  node((0, 1), [$cC(sigma)$]),
  node((1, 0), [$cC' (tau)$]),
  node((1, 1), [$cC' (sigma),$]),
  arr((0, 0), (0, 1), [$[sigma : tau] dot cC(tau >= sigma)$]),
  arr((1, 0), (1, 1), [$[sigma : tau] dot cC'(tau >= sigma)$]),
  arr((0, 0), (1, 0), [$Phi_tau$]),
  arr((0, 1), (1, 1), [$Phi_sigma$]),
))
  which commutes by @morphism-of-cosheaves.
]

#corollary[
  $Phi : cC -> cC'$ induces a map on homology groups $bH_cx Phi : bH_cx (K; cC) -> bH_cx (K; cC')$.
]
#proof[
  By the functoriality of homology, i.e., @notes[Proposition 4.7].
]

#definition[
  Let $Phi : cC -> cC'$ be a morphism of cosheaves.
  - $Phi$ is a *monomorphism* when each $Phi_tau : cC(tau) -> cC'(tau)$ is injective;
  - $Phi$ is an *epimorphism* when each $Phi_tau : cC(tau) -> cC'(tau)$ is surjective; and
  - $Phi$ is an *isomorphism* when each $Phi_tau : cC(tau) -> cC'(tau)$ is an isomorphism.

  We also say that $Phi$ is a *strict monomorphism* (resp. *strict epimorphism*) if $Phi$ is a monomorphism (resp. epimorphism) but is not an isomorphism.
]
#proposition[
When $Phi: cC -> cC'$ is an isomorphism, its inverse $Phi^(-1) : cC' -> cC$ consists of $(Phi_tau)^(-1) : cC'(tau) -> cC(tau)$ for each simplex $tau$ in $K$. 
]
#proof[
  We need to check that $Phi^(-1)$ is indeed a natural transformation. For each pair $tau >= sigma$, the naturality of $Phi$ says that 
  $
    cC' (tau >= sigma) oo Phi_tau = Phi_sigma oo cC (tau >= sigma).
  $
  Hence 
  $
    (Phi_sigma)^(-1) oo cC' (tau >= sigma)  =   cC (tau >= sigma) oo (Phi_tau)^(-1),
  $
  which shows the naturality of $Phi^(-1)$. 
]

= Task 3

#lemma[
  The constant cosheaf $underline(FF)_K$ gives the same homology groups as the standard homology.
]
#proof[
  In this case, 
  $bC_k (K; FK) = product_(dim tau = k) FF.
  $
  This agrees with @notes[Definition 3.6]. It is also easy to see the boundary maps agree with @notes[Definition 3.7]. #TODO[show?]
]

#example[
  Let $V = {v}$ and 
  let $K$ be the simplicial complex ${tau}$, where $tau = {v}$. Let $cC : (K, >=) -> VF$ be the cosheaf which assigns the zero vector space to the only simplex $tau = {v}$ in $K$. Then $K$ has standard homology of a single point, which agrees with the homology induced by $FK$. On the other hand,  the chain complex induced by $cC$ has $cC_k (K; cC) = 0$ for all $k >= 0$, so $bH_k (K ; cC) = 0$ for all $k >= 0$. Thus $FK$ has the homology of a single point, but $cC$ does not.
]

#example[
  Let $V = {v_1, v_2}$ and let $K = {tau_1, tau_2}$, where $tau_1 = {v_1}$ and $tau_2 = {v_2}$. Let $cC$ be the cosheaf such that $cC(tau_1) = FF$ and $cC(tau_2) = 0$. (There is no non-trivial face relation in $K$.) Then  with $FK$-coefficients, $K$ has chain complex $ bC_k (K ; FK) = cases(FF^2 quad &"if" k = 0 comma, 0 quad &"otherwise,") $ with all the boundary maps necessarily zero, which gives 
  $
    bH_k (K ; FK) = cases(FF^2 quad &"if" k = 0 comma, 0 quad &"otherwise.")
  $
  On the other hand, with $cC$-coefficients, we similarly see that 
  $ bH_k (K ; cC) = bC_k (K ; cC) = cases(FF quad &"if" k = 0 comma, 0 quad &"otherwise.") $
  Thus $FK$ does not have the homology of a single point, but $cC$ does. 
]

#TODO[what is strict monomorphism? each component is injective or some component is injective?]

#example[
  Let $V = {v_1, v_2}$ and $K = {tau_1, tau_2, tau_3}$, where $tau_1 = {v_1}$, $tau_2 = {v_2}$ and $tau_3 = {v_1, v_2}$. (In other words, $K = Delta(1)$.) Define cosheaf $cC$  as follows: 
  $
    tau_1 &mapsto FF, \
    tau_2 &mapsto FF^2, \
    tau_3 &mapsto FF^2, \
    (tau_3 >= tau_1) &mapsto ((a, b) |-> a), \
    (tau_3 >= tau_2) &mapsto id_(FF^2). \
  $
  There is no non-trivial face relation composition in $K$, so $cC$ is easily seen to be a cosheaf.

  We then define morphism $Phi : FK -> cC$ as follows: $Phi_(tau_1) = id_FF$, $Phi_(tau_2) (a) = (a, 0)$ and $Phi_(tau_3) (a) = (a, 0)$. 
  Since the following diagram commutes 
// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBoBGAXVJADcBDAGwFcYkQAxDkAX1PUy58hFOQrU6TVuy4A9AEy9+IDNjwEi88TQYs2iThwVKBa4UTLEJu6Qa4mVg9SORirOqfsMPVQjSi13ST0Zbh4JGCgAc3giUAAzACcIAFskABYaHAgkAGYPEIMsKAB9ez4E5LTETJBspABWAtsQYrKw5STUpDE6nMQyYJaACnpSACMASgAfAFoAPnoHLure+sQtIa9RiZmFnanlqsas-s2bL3oAAjn5q53iSaPuxHy+pEGL9jbyzuOa049ZqXG4Le5jR68Sg8IA
#align(center, commutative-diagram(
  node-padding: (90pt, 50pt),
  node((1, 0), [$FF$]),
  node((1, 1), [$FF^2$]),
  node((1, 2), [$FF^2,$]),
  node((0, 0), [$FF$]),
  node((0, 1), [$FF$]),
  node((0, 2), [$FF$]),
  arr((0, 1), (0, 0), [$id_FF$]),
  arr((0, 1), (0, 2), [$id_FF$]),
  arr((1, 1), (1, 0), [$(a,b)|->a$]),
  arr((1, 1), (1, 2), [$id_(FF^2)$]),
  arr((0, 2), (1, 2), [$a |-> (a,0)$]),
  arr((0, 0), (1, 0), [$id_FF$]),
  arr((0, 1), (1, 1), [$a |-> (a,0)$]),
))
  we see that $Phi$ is indeed a natural transformation. Further, each component of $Phi$ is injective but $Phi$ is not an isomorphism, so $Phi$ is a strict monomorphism.
  
  $K = Delta(1)$, so by @notes[Proposition 2.6], $K$ has the same homology groups with $FK$-coefficients as a single point. We then compute the chain complex of $K$ with $cC$-coefficients: $ bC_0 (K ; cC) = cC(tau_1) plus.circle cC(tau_2) = FF^3, $ $ bC_1 (K ; cC) = cC(tau_3) = FF^2, $ and the only non-trivial boundary map $diff_1^cC$ sends $(a, b)$ to $(a, -a, -b)$. Thus $Ker diff_1^cC = 0$ and $Im diff_1^cC = FF^2$, and thus $bH_0 (K; cC) = FF^3 over FF^2 = FF$ and $bH_1 (K ; cC) = 0$. Finally, since $Phi_0 : bC_0 (K; FK) ->  bC_0 (K; cC)$ is injective, which in particular does not send any generator of $bH_0 (K; FK)$ to zero, the induced map $bH_0 (K; FK) -> bH_0 (K; cC)$ is then necessarily an isomorphism $FF -> FF$. This is the only non-trivial map in $bH_cx (K; FK) -> bH_cx (K; cC)$, which is thus an isomorphism.
]

#proposition[
  For any simplicial complex $K$ and any cosheaf $cC$ over $K$,
  there does not exist a strict epimorphism $Phi : FK -> cC$ which induces an isomorphism on homology.
]

#proof[
  Suppose such $Phi$ exists, then there exists a simplex $tau$ in $K$ such that $Phi_tau : FF -> cC(tau)$ is surjective but is not an isomorphism. Then $Phi_tau$ is necessarily the zero map $FF -> cC(tau) = 0$. 

  We then claim that for any simplex $sigma$ in $K$ such that $tau >= sigma$, $Phi_sigma = 0$ and $cC(sigma) = 0$. By the naturality of $Phi$, the following commutes:

  #align(center, commutative-diagram(
  node-padding: (70pt, 50pt),
  node((0, 0), [$FF$]),
  node((1, 0), [$FF$]),
  node((0, 1), [$cC(tau)$]),
  node((1, 1), [$cC(sigma),$]),
  arr((0, 0), (1, 0), [$id_FF$]),
  arr((0, 1), (1, 1), [$cC(tau >= sigma)$]),
  arr((0, 0), (0, 1), [$Phi_tau = 0$]),
  arr((1, 0), (1, 1), [$Phi_sigma$]),
))
  which forces the surjective $Phi_sigma : FF -> cC(sigma)$ to also be the zero map, and thus $cC(sigma) = 0$. 
  
  This in particular shows that there must be some vertex $rho = {v}$ such that $Phi_rho = 0$ and $cC(rho) = 0$. Then in the chain map, $Phi_0 : bC_0 (K ; FK) -> bC_0 (K; cC)$ sends $rho$ to $0$. However, $rho$ can be seen as a generator of $bH_0 (K; FK)$, representing the connected component to which $rho$ belongs. Then the induced map $bH_0 (K; FK) -> bH_0 (K; cC)$ on homology would also send the class of $rho$ to $0$ and thus cannot be an isomorphism. We have therefore reached a contradiction.
]

= Task 4

#definition[
  Let $cC$ be a cosheaf over a simplicial complex $K$. Then a *filtration* of $K$ of length $l >= 1$ is a collection of cosheaves $ {cC^1, cC^2, ..., cC^l = cC} $ over $K$ together with strict monomorphisms $Psi_i : cC^i -> cC^(i+1)$ for each $i = 1, 2, ..., l-1$. 
  // We denote such a filtration as 
  // $
  //   cC^1 subset cC^2 subset ... subset cC^l = cC.
  // $
]

Then for each dimension $k >= 0$, there are induced maps on homology 
$
  bH_k (K ; cC^1) ->^(bH_k Psi_1) bH_k (K ; cC^2) ->^(bH_k Psi_2)  ... ->^(bH_k Psi_(l-1)) bH_k (K ; cC^l)
$
For any $1 <= i <= j <= l$, we denote $Psi_(i->j) = Psi_(j-1) oo ... oo Psi_i$ (when $i = j$, $Psi_(i -> i) = id_(cC^i)$) and then
$
  bH_k Psi_(i->j) = bH_k Psi_(j-1) oo ... oo bH_k Psi_i.
$

For any $1 <= i <= j <= l$, the *persistent homology* is given by 
$
  PH_(i->j)
$
#TODO[tomorrow...]




#pagebreak()
#bibliography("bib.yml")