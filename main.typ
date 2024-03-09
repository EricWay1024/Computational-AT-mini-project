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
  Let $V = {v_1, v_2}$ and let $K = {tau_1, tau_2}$, where $tau_1 = {v_1}$ and $tau_2 = {v_2}$. Let $cC$ be the cosheaf such that $cC(tau_1) = FF$ and $cC(tau_2) = 0$. (There is no face relation in $K$.) Then  with $FK$-coefficients, $K$ has chain complex $ bC_k (K ; FK) = cases(FF^2 quad &"if" k = 0 comma, 0 quad &"otherwise,") $ with all the boundary maps necessarily zero, which gives 
  $
    bH_k (K ; FK) = cases(FF^2 quad &"if" k = 0 comma, 0 quad &"otherwise.")
  $
  On the other hand, with $cC$-coefficients, we similarly see that 
  $ bH_k (K ; cC) = bC_k (K ; cC) = cases(FF quad &"if" k = 0 comma, 0 quad &"otherwise.") $
  Thus $FK$ does not have the homology of a single point, but $cC$ does. 
]

#TODO[what is strict monomorphism? ]

#example[

]

#pagebreak()
#bibliography("bib.yml")