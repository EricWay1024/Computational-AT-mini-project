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
  The *constant* cosheaf $underline(V)_K$ is the functor given as follows:  
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
  For each $k>=0$ and any $k$-simplices  $tau$ and $tau'$  in $K$, define $Phi_k : bC_k (K; cC) -> bC_k (K; cC')$ as the linear map whose $cC(tau) -> cC'(tau')$ component is 
  $
    cases(Phi_tau quad & tau = tau' comma, 
    0 quad &  "otherwise".)
  $
  We claim that ${Phi_k}_(k>=0)$ is a chain map $bC_cx (K; cC) -> bC_cx (K; cC')$, i.e., the following diagram commutes:

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

// #TODO[what is strict monomorphism? each component is injective or some component is injective?]

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
  Let $cC$ be a cosheaf over a simplicial complex $K$. Then a *filtration* ${cC^i}$ of $cC$ over $K$ of length $l >= 1$ is a collection of cosheaves ${cC^1, cC^2, ..., cC^l = cC} $ over $K$ together with strict monomorphisms $Psi^i : cC^i -> cC^(i+1)$ for each $i = 1, 2, ..., l-1$. 
  // We denote such a filtration as 
  // $
  //   cC^1 subset cC^2 subset ... subset cC^l = cC.
  // $

Then for each dimension $k >= 0$, there are induced maps on homology 
$
  bH_k (K ; cC^1) ->^(bH_k Psi^1) bH_k (K ; cC^2) ->^(bH_k Psi^2)  ... ->^(bH_k Psi^(l-1)) bH_k (K ; cC^l)
$
For any $1 <= i <= j <= l$, we denote $Psi^(i->j) = Psi^(j-1) oo ... oo Psi^i$ (when $i = j$, $Psi^(i -> i) = id_(cC^i)$) and by the functoriality of homology,
$bH_k Psi^(i->j) = bH_k Psi^(j-1) oo ... oo bH_k Psi^i.
$
Then the associated *persistent homology* of $K$ with coefficients in ${cC^i}$ is defined by 
$
  PH_(k) Psi^(i->j) = Im(bH_k Psi^(i->j)),
$
which is a subspace of $bH_k (K; cC^j)$. 
]

#lemma[
If $cC = FK$, a filtration ${cC^i}$ of $K$ defined as above is the same as a filtration defined as in @notes[Definition 1.6].
]

#proof[
  Since all $Phi_i$'s are strict monomorphisms, each $cC^i$ would only assign either $FF$ or $0$ to each simplex in $K$. Also, for any $i$ and any pair $tau >= sigma$, if $cC^i (tau) = FF$, then $Psi^(i->l)_(tau) = id_FF$ by injectivity, and the naturality of $Psi^(i -> l)$ would ensure that $cC^i (sigma) = FF$ as well. This indicates that for each $i$, the simplices in $K$ to which $cC^i$ assigns $FF$ form a subcomplex of $K$, which can be viewed as $bF_i K$ as in @notes[Definition 1.6]. 
]
= Task 5
The following is based on @notes[Section 8.1].

#definition[
  A *partial matching* on $K$ is a collection $Sigma$ of simplex-pairs $sigma lt.tri tau$ of $K$ such that each simplex in $K$ only occurs in any of the pairs at most once. A simplex in $K$ is said to be a *critical simplex* if it does not occur in any of the pairs in $Sigma$.
]
#definition[
  A *$Sigma$-path* is a zigzag sequence of distinct simplices in $K$ of the form 
  $
    rho = (sigma_1 lt.tri tau_1 gt.tri sigma_2 lt.tri tau_2 gt.tri ... gt.tri sigma_m lt.tri tau_m ),
  $
  where $(sigma_j lt.tri tau_j)$ lies in $Sigma$ for each $j = 1, 2, ..., m$.  Such a $Sigma$-path $rho$ is a *$Sigma$-cycle* if $m > 1$ and $tau_m lt.tri sigma_1$. Any $Sigma$-path which is not a $Sigma$-cycle is a *gradient path*. 
]

#definition[
  A partial matching $Sigma$ on $K$ is said to be *acyclic* if there does not exist any $Sigma$-cycle.
]


#definition[
  Let ${cC^i}$ be a filtration of $cC$ over $K$ of length $l >= 1$. An acyclic partial matching $Sigma$ on $K$ is *compatible* with ${cC^i}$ if for any $1<= i <= l$ and any pair $sigma lt.tri tau$ in $Sigma$, the map $cC^i  (tau >= sigma)$ is an isomorphism.
]
// #definition[
//   Given an acyclic partial matching $Sigma$ on $K$ which is compatible with ${cC^i}$,  for each $1 <= i <= l$, a simplex $tau$ in $K$ is said to be a *critical simplex* if $tau$ does not occur in any of the pairs in $Sigma$.
//   // + $cC^i (tau) != 0$.
// ]
// #TODO[is this a helpful definition ? do we want to omit definition (2)?]

#example[
  #TODO[maybe write some code]
]

= Task 6

Fix a filtration ${cC^i}$ of $cC$ over $K$ of length $l >= 1$ and  an acyclic matching $Sigma$ on $K$ compatible with ${cC^i}$. Until further notice, also fix $i$ such that $1<= i<= l$.

#definition[
  Define $cC^i_(alpha, beta) : cC(alpha) -> cC(beta)$ as 
  $
    cC^i_(alpha, beta) = [beta : alpha] dot cC^i (alpha >= beta) = cases(
      + cC^i (alpha >= beta) quad & beta = alpha_(-j) "for even " j comma ,
      - cC^i (alpha >= beta) quad & beta = alpha_(-j) "for odd " j comma , 
      0 quad & "otherwise." 
    )
  $
  ]
  #definition[
  For a $Sigma$-path
     $
    rho = (sigma_1 lt.tri tau_1 gt.tri sigma_2 lt.tri tau_2 gt.tri ... gt.tri sigma_m lt.tri tau_m ),
  $
  define its *$cC^i$-weight* $w_(cC^i)(rho)$ as the linear map $cC^i (sigma_1) -> cC^i (tau_m)$ given by 
  $
    w_(cC^i)(rho) := (-1)^m dot (cC_(tau_m, sigma_m)^i)^(-1) oo ... oo (cC_(tau_2, sigma_2)^i)^(-1) oo cC_(tau_1, sigma_2)^i oo (cC_(tau_1, sigma_1)^i)^(-1).
  $
]
#remark[
  Since $cC^i_(tau_j, sigma_j) = plus.minus cC^i (tau_j >= sigma_j)$ for each $1 <= i <= l$ and $1 <=  j <= m$ is by definition an isomorphism, taking its inverse is justified.
]

#definition[
  The *Morse complex* of $Sigma$ with coefficients in $cC^i$ is a sequence 
  $
    (bC_cx^Sigma (K; cC^i), d_cx ^(cC^i, Sigma) ),
  $
  where for each dimension $k >= 0$,
  $
    bC_k^Sigma (K; cC^i) = product_(dim alpha = k comma \ alpha "critical ") cC^i (alpha),
  $
  and for critical simplices $alpha, beta$ in $K$ with $dim alpha = k$ and $dim beta = k-1$, 
  $d_k ^(cC^i, Sigma) : bC_k^Sigma (K; cC^i) -> bC_(k-1)^Sigma (K; cC^i)$  has the following $cC^i (alpha) -> cC^i (beta)$ component:
  $
    d_k ^(cC^i, Sigma)|_(alpha, beta) = cC^i_(alpha, beta) + sum_(Sigma"-path" rho = (sigma lt.tri ... lt.tri tau)) cC^i_(tau, beta) oo w_(cC^i)(rho) oo cC^i_(alpha, sigma).
  $
]
#notation[
  As the notations get visibly messy,
  from now on, with $K$, ${cC^i}$ and $Sigma$ fixed as above, for each $1 <= i <= l$ and each dimension $k >=0$, 
  denote $ bC_k^i := bC_k (K ; cC^i) comma quad diff_k^i := diff_k^(cC^i) comma \ 
  bM_k^i  := bC_k^Sigma (K; cC^i), quad  d_k^i := d_k^(cC^i, Sigma) . $ 
  We also denote $w_i (rho) := w_(cC^i) (rho)$ for any $Sigma$-path $rho$.
]
#proposition[
  For each $i$, the Morse complex $(bM_cx^i, d^i_cx)$ is a chain complex.
]
#let ci(s, t) = [$cC^i_(#s, #t)$] 
#proof[
  This is analogous to @notes[Proposition 8.8]. To elaborate, it suffices by induction to consider when $Sigma = {(sigma lt.tri tau)}$, the set of critical simplices $C_Sigma = K - {sigma, tau}$, and the only $Sigma$-path $rho = (sigma lt.tri tau)$. Then we need to show that for each $k >= 2$, for any $alpha, omega in C_Sigma$ such that $dim alpha = dim omega + 2 = k$, we have $ B := sum_(dim xi = k - 1 comma \ xi in C_Sigma) d^i_(k-1) |_( xi, omega) oo  d^i_k |_(alpha , xi) = 0. $
  For each $xi$ in the sum, denote $B_xi := d^i_(k-1) |_( xi, omega) oo  d^i_k |_(alpha , xi)$, which by definition expands to 
  $
    B_xi = 
    underbrace( ci(xi, omega) oo ci(alpha, xi), B_(xi, 1))
    underbrace(- ci(tau, omega) oo (ci(tau, sigma))^(-1) oo ci(xi, sigma) oo ci(alpha, xi) , B_(xi, 2))
    underbrace(
    -ci(xi, omega) oo ci(tau, xi) oo (ci(tau, sigma))^(-1) oo ci(alpha, sigma), 
    B_(xi, 3)) \ + ci(tau, omega) oo (ci(tau, sigma))^(-1) oo ci(xi, sigma) oo ci(tau, xi) oo (ci(tau, sigma))^(-1) oo ci(alpha, sigma),
  $
  where the fourth term is always zero, since $ci(alpha, sigma) != 0$ only if $dim sigma = k-1$, but $ci(xi, sigma) != 0$ only if $dim sigma = k-2$. Now denote the first three terms of $B_xi$ as $B_(xi, j)$ for $j = 1, 2, 3$ respectively, so $B_xi = sum_(j=1)^3 B_(xi, j)$. Since $diff^i_cx$ is a boundary operator, we have $ sum_xi B_(xi, 1) = - ci(tau, omega) oo ci(alpha, tau) -  ci(sigma, omega) oo ci(alpha, sigma). $
  We then see that $sum_xi B_(xi, j) = 0$ for any $j = 1, 2, 3$ if $dim sigma != k - 2$ and $dim sigma != k-1$. Then there remain two cases:
  - If $dim sigma = k-2$ and so $dim tau = k -1$, then $B_(xi, 3) = 0$ for any $xi$ in the sum, and $ sum_xi B_(xi, 2) =  ci(tau, omega) oo (ci(tau, sigma))^(-1) oo ci(tau, sigma) oo ci(alpha, tau) =  ci(tau, omega) oo ci(alpha, tau), $
    which would cancel with $sum_xi B_(xi, 1)$;
  - If $dim sigma = k -1$, the situation is similar as above, with $B_(xi, 2) = 0$ for any $xi$ and also $sum_xi B_(xi, 3) $ cancelling with $sum_xi B_(xi, 1) $.
  Therefore, we conclude that $B = sum_xi B_xi = 0$ as desired.
]

#proposition[
  For each $i$, the Morse complex $(bM_cx^i, d^i_cx)$ is chain homotopy equivalent to the chain complex $(bC_cx^i, diff^i_cx)$.
]
#proof[
  This is analogous to @notes[Proposition 8.10] and @notes[Lemma 8.11]. We first consider the case when $Sigma = {(sigma lt.tri tau)}$. For each $k >= 0$ and for each pair of $k$-simplices $(alpha, omega) in K times C_Sigma$, define the $cC^i  (alpha) -> cC^i (omega)$ component of the linear map $psi^i_k : bC_k^i -> bM_k ^i$  by 
  $
    psi^i_k |_(alpha, omega) = cases(
      id_(cC^i (alpha)) quad & alpha = omega != tau comma, 
      - ci(tau, omega) oo (ci(tau, sigma))^(-1) quad & alpha = sigma comma , 
      0 & "otherwise".
    ) 
  $
  Conversely, define the $cC^i (omega) -> cC^i (alpha)$ component of the linear map $phi^i _k : bM_k ^i -> bC_k ^i$ by 
  #math.equation(block: true, numbering: "(1)", supplement: "Equation",
  $
    phi^i_k |_(omega, alpha) = cases(
      id_(cC^i (omega)) quad & omega =  alpha != sigma comma, 
      -  (ci(tau, sigma))^(-1) oo ci(omega, sigma)   quad & alpha= tau comma , 
      0 & "otherwise".
    )
  $) <def-phi>
  
  One can verify that $psi^i_cx$ and $phi^i_cx$ are two chain maps.
  //  #TODO[...] 
  We then note that $psi^i_k oo phi^i_k$ is the identity map on $bM^i_k$. Indeed, for each $omega, omega' in bM_k^i$, 
  $
    (psi^i_k oo phi^i_k)|_(omega, omega') = sum_(alpha in bC_k^i) psi^i_k |_(alpha, omega') oo phi^i_k |_(omega, alpha).
  $
  If $alpha = sigma$, then $phi^i_k |_(omega, alpha) = 0$. If $alpha = tau$, then $psi^i_k |_(alpha, omega') = 0$. Thus we only need to consider the case when $alpha in.not {tau, sigma}$. Then we see that if $omega != omega'$, one of $psi^i_k |_(alpha, omega')$ and $ phi^i_k |_(omega, alpha)$ must be $0$; if $omega = omega'$, we have $psi^i_k |_(alpha, omega') oo phi^i_k |_(omega, alpha) = id_(cC^i (omega))$ only if $alpha = omega = omega'$. 

  Similarly, we can find that for each $alpha, alpha' in bC_k^i$, 
  $
    (phi^i_k oo psi^i_k)|_(alpha, alpha') = cases(
      - ci(tau, alpha') oo (ci(tau, sigma))^(-1) quad & alpha = tau != alpha' comma, 
      - (ci(tau, sigma))^(-1) oo ci(alpha, sigma) quad & alpha != sigma = alpha' comma,
      id_(cC^i (alpha)) quad & alpha = alpha' comma , 
      0 quad & "otherwise".  
    )
  $
  Then the linear maps $theta_k : bC_k^i -> bC_(k+1)^i$, whose $cC(alpha) -> cC(beta)$ component for $k$-simplex $alpha$ and $(k+1)$-simplex $beta$ is defined as 
  $
    theta_k |_(alpha, beta) = cases(
      (ci(tau, sigma))^(-1) quad & alpha = sigma "and" beta = tau comma, 
      0 quad & "otherwise" comma
    )
  $
  gives a chain homotopy between $phi^i_k oo psi^i_k$ and the identity chain map on $bC_k^i$.

  Then to move on to general cases of $Sigma$, the discussion at the end of @notes[Section 8.3] also applies with slight modification. 
  // #TODO[do we want to write more?]
]
#corollary[
  For each $i$ and each dimension $k>=0$, $phi^i_k$ induces an isomorphism from  $bH_k (bM^i_cx)$ to $bH_k (bC^i_cx)$.
]
<iso-homo>

We now introduce a useful (and beautiful) diagram:

#figure(caption: "The commutative cube.")[
// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRACMBhAfQGsA9AFYgAvqXSZc+QijIBGKrUYs2XbgApeAajkBKIaPEgM2PASIAmcovrNWiDj00796wbsMTT0y6QXVbFQc1Zz1+NxdPY0kzGWQ5UgsbZXsOAFkNXld3KJMpcxQAZkTku1UM0OyPMS98uITC0qD0zJdwnJro7wLkYsaAlPLWsIi9UUUYKABzeCJQADMAJwgAWyQEkBwIJDIlMocoLHn54f1hTqXVneotpCs95oAFbD4DC+W1xA3bxGKH1OeWFObyMl0+fx+90CqUOx2Bo2qoI+SAALDdtogAKwDfabLAMWDqQG6V7nJFXRAANnRSAA7DjmngCTAidgSZUQQtkVSaYg0f82EzCbD5uztGFhNQGHR2DAGI8Yj4HIssFMABY4KJgum87EChxClkisVtBEgKUyuUK7oyEAq9Wa94U-k-XY4Oj4thqiAQXha7nUzYY74ehhen1+p2fPWQm6h8O+-0U+lBpAQ+MOb2JkQUERAA
#align(center, commutative-diagram(
  node-padding: (50pt, 50pt),
  node((0, 0), [$bC_(k-1)^i$]),
  node((1, 0), [$bC_(k)^i$]),
  node((0, 2), [$bC_(k-1)^(i+1)$]),
  node((1, 2), [$bC_(k)^(i+1)$]),
  node((2, 1), [$bM_(k-1)^(i)$]),
  node((2, 3), [$bM_(k-1)^(i+1)$]),
  node((3, 1), [$bM_(k)^(i)$]),
  node((3, 3), [$bM_(k)^(i+1)$]),
  arr((1, 0), (0, 0), [$diff_(k)^i$]),
  arr((0, 0), (0, 2), [$Psi_(k-1)^i$]),
  arr((1, 0), (1, 2), [$Psi_(k)^i$]),
  arr((1, 2), (0, 2), [$diff_(k)^(i+1)$]),
  arr((2, 1), (2, 3), [$tilde(Psi)_(k-1)^i$]),
  arr((3, 1), (3, 3), [$tilde(Psi)_(k)^i$]),
  arr((3, 1), (2, 1), [$d_(k)^i$], label-pos: right),
  arr((3, 3), (2, 3), [$d_(k)^(i+1)$], label-pos: right),
  arr((2, 1), (0, 0), [$phi_(k-1)^i$], label-pos: left, ),
  arr((3, 1), (1, 0), [$phi_(k)^i$], ),
  arr((2, 3), (0, 2), [$phi_(k-1)^(i+1)$], label-pos: right),
  arr((3, 3), (1, 2), [$phi_(k)^(i+1)$]),
))
]
<cube>
In @cube, we have shown that back face commutes, since each $Psi^i_cx$ is a chain map; the left face (as well as the right face) commutes, since each $phi_cx^i$ is a chain map; and furthermore, each slant arrow $phi^i_k$ induces an isomorphism on homology.
To show the commutativity of the remaining faces,
now we consider what happens when we vary $i$, the stage of the filtration. 

#proposition[
  Each $Psi^i : cC^i -> cC^(i+1)$ induces a chain map $ tilde(Psi)^i_cx : bM_cx^i -> bM_cx^(i+1). $ In other words,  the front face of @cube commutes.
]
<front-commute>
#proof[
  For each dimension $k >= 0$,
  for an arbitrary pair of critical $k$-simplices $alpha, alpha'$, define the $cC^i  (alpha) -> cC^(i+1) (alpha')$ component of the linear map $tilde(Psi)^i_k : bM_k^i -> bM_k^(i+1)$ as 
  $
    cases(
      Psi^i_alpha quad & alpha = alpha' comma , 
      0 quad & "otherwise".
    )
  $
  Then it suffices to show for any critical $k$-simplex $alpha$ and critical $(k-1)$-simplex $beta$, 
  $
    d_k^(i+1) |_(alpha, beta) oo Psi_alpha^i = Psi_beta^i oo d_k^(i) |_(alpha, beta),
  $
  which by definition expands  to 
  #math.equation(block: true, numbering: "(1)", supplement: "Equation",
  $
         (cC^(i+1)_(alpha, beta) + sum_(Sigma"-path" rho = (sigma lt.tri ... lt.tri tau)) cC^(i+1)_(tau, beta) oo w_(i+1)(rho) oo cC^(i+1)_(alpha, sigma)) oo 
Psi_alpha^i = \ Psi_beta^i oo
(        cC^i_(alpha, beta) + sum_(Sigma"-path" rho = (sigma lt.tri ... lt.tri tau)) cC^i_(tau, beta) oo w_(i)(rho) oo cC^i_(alpha, sigma)).
  $) <eq1>
  
  

   Notice that for any simplices $delta >= gamma$ in $K$, by the naturality of $Psi^i$, we have 
   $cC^(i+1) (delta >= gamma) oo Psi^i_(delta) = Psi^i_(gamma) oo cC^i (delta >= gamma)$. Hence, for an arbitrary pair of simplices $ delta, gamma$ in $K$,
   #math.equation(block: true, numbering: "(1)", supplement: "Equation",
   $ cC^(i+1) _(delta, gamma) oo Psi^i_(delta) = Psi^i_(gamma) oo cC^i_ (delta , gamma). $ ) <eq2>

   In particular, if $(gamma lt.tri delta) in Sigma$, then by compatibility, both $cC^(i+1) _(delta, gamma)$ and $cC^i_ (delta , gamma)$ are isomorphisms, and we have #math.equation(block: true, numbering: "(1)", supplement: "Equation",
   $
        (cC^(i+1) _(delta, gamma))^(-1) oo Psi^i_(gamma) = Psi^i_(delta) oo (cC^i_ (delta , gamma))^(-1). 
   $) <eq3>
   
  Finally, note that each $w_(i+1) (rho)$ consists of nothing but compositions of $cC^(i+1) _(ast, ast)$ or its inverse, apart from a sign.
  So for each summand on the LHS of @eq1, we can imagine passing $Psi_alpha^i$ step-by-step from right to left using @eq2 or @eq3, changing the superscript $(i+1)$ to $i$ at each step, and eventually $Psi_alpha^i$ becomes $Psi_beta^i$ on the far left, which is exactly a corresponding summand on the RHS of @eq1.
]

#proposition[
  The bottom face (hence as well as the top face) of @cube commutes. 
]
#proof[
  By induction, it suffices to consider $Sigma = {(sigma lt.tri tau)}$.
  It then suffices to show for any critical $k$-simplex $omega$ and any $k$-simplex $alpha$ that 
  $
   phi_k^(i+1) |_(omega, alpha) oo Psi_omega^i = Psi_alpha^i oo phi_k^i |_(omega, alpha).
  $
  Expand the above using @def-phi, and the proof for @front-commute would also work, again thanks to the naturality of $Psi^i$.
]

#theorem[
  For each $k >= 0$, $bC_k^cx$ and $bM_k^cx$ induce the same persistent homology.
]
#proof[
  We have shown that @cube commutes. In other words, in the category of chain complexes, we have the following commutative diagram: 
// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRACMBhAfQGMAPAHpYQAX1LpMufIRQBGclVqMWbLnyEAKLAGo5ASjESQGbHgJEycpfWatEHALIbhRyWZlEF16rdUP2ZwFBbT1DUSUYKABzeCJQADMAJwgAWyQyEBwIJAVlOzYABWxhDTcQZLSkACZqbKQAZl8VeyysBlhNYqx9UoFyyvTEWqycxEy-VrQACywXEXFElKGm0dzmgocZueDQgzEKUSA
#align(center, commutative-diagram(
  node-padding: (50pt, 50pt),
  node((0, 0), [$bC_cx^i$]),
  node((0, 1), [$bC_cx^(i+1)$]),
  node((1, 0), [$bM_cx^i$]),
  node((1, 1), [$bM_cx^(i+1).$]),
  arr((0, 0), (0, 1), [$Psi^i_cx$]),
  arr((1, 0), (1, 1), [$tilde(Psi)^i_cx$]),
  arr((1, 0), (0, 0), [$phi_cx^i$]),
  arr((1, 1), (0, 1), [$phi_cx^(i+1)$]),
))
By the functoriality of homology, for each dimension $k >= 0$, we have the following commutative diagram:
// https://t.yw.je/#N4Igdg9gJgpgziAXAbVABwnAlgFyxMJZABgBpiBdUkANwEMAbAVxiRACMAJAfQGsACABQBjAMIA9LAEoQAX1LpMufIRQBGclVqMWbLn0HsJgrAGo1UmfMXY8BImTVb6zVog48BhgLKSrCkAxbFSINJ2oXXXd9L3ZfE3NLOS0YKABzeCJQADMAJwgAWyQyEBwIJA1tVz1PfgAFbEk5ALzCpAAmajKkAGYInTcPPn48BlhBBukm6xBWosRO0vLEEsjBmP40AAssaZb8+b6liv7q6Nrt3YSLZNkgA
#align(center, commutative-diagram(
  node-padding: (50pt, 50pt),
  node((0, 0), [$bH_k (bC^i)$]),
  node((0, 1), [$bH_k (bC^(i+1))$]),
  node((1, 0), [$bH_k (bM^i)$]),
  node((1, 1), [$bH_k (bM^(i+1)).$]),
  arr((0, 0), (0, 1), [$bH_k Psi^i$]),
  arr((1, 0), (1, 1), [$bH_k tilde(Psi)^i$]),
  arr((1, 0), (0, 0), [$bH_k phi^i$]),
  arr((1, 1), (0, 1), [$bH_k phi^(i+1)$], label-pos: right),
))
By @iso-homo, each vertical line is an isomorphism between homology groups, so each $bH_k tilde(Psi)^i$ would have an isomorphic image as $bH_k Psi^i$. So we are done.
]


#bibliography("bib.yml")