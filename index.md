## Fitch-Style Modal Calculi

In type systems, a modality can be broadly construed as a unary type constructor with certain properties. Type systems with modalities have found a wide range of applications in programming languages to capture and specify properties of a program in its type. In this work, we study typed lambda calculi equipped with a necessity modality (denoted by ☐) formulated in the so-called Fitch style. The necessity modality, which originates from modal logic, has found applications in partial evaluation and staged computation, information-flow control, and recovering purity in an impure functional language.

Fitch-style modal lambda calculi feature necessity modalities in a typed lambda calculus by extending the typing context with a delimiting “lock” operator (denoted by 🔒). The lock operator simplifies formulation of typing rules for calculi that incorporate different modal axioms. These calculi have excellent computational properties, but each variant demands different, tedious and seemingly ad hoc treatment to prove meta-theoretic properties such as normalization. In this work, we identify the possible-world semantics of Fitch-style calculi and use it to develop normalization. The possible-world semantics enables a uniform treatment of Fitch-style calculi by isolating their differences to a specific parameter that identifies the modal fragment.

### Papers & Abstracts

* Normalization for Fitch-Style Modal Calculi  
  [ICFP 2022](https://icfp22.sigplan.org/) (<span style="color:IndianRed">Distinguished paper award</span>)  
  Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas  
  Article: [Authors' version](https://nachivpn.me/nfmc.pdf), [arXiv](https://doi.org/10.48550/arXiv.2207.12807), [PACMPL](https://doi.org/10.1145/3547649)  

* Semantic Analysis of Normalization by Evaluation for Fitch-Style Modal Calculi (extended abstract)  
  [TYPES 2021](https://types21.liacs.nl/)  
  Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas  
  Article: [Authors' version](https://nachivpn.me/types21.pdf); Talk video: [YouTube](https://www.youtube.com/watch?v=2OJBBWLYTQA)

### Artifacts

* Agda mechanization  
  Source: [Browseable code](html/Everything.html), [Github repo](https://github.com/nachivpn/k)
