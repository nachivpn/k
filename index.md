## Fitch-Style Modal Calculi

In type systems, a modality can be broadly construed as a unary type constructor with certain properties. Type systems with modalities have found a wide range of applications in programming languages to capture and specify properties of a program in its type. In this work, we study typed lambda calculi equipped with a necessity modality (denoted by ☐) formulated in the so-called Fitch style. The necessity modality, which originates from modal logic, has found applications in partial evaluation and staged computation, information-flow control, and recovering purity in an impure functional language. 

Fitch-style modal lambda calculi feature necessity modalities in a typed lambda calculus by extending the typing context with a delimiting “lock” operator (denoted by 🔒). The lock operator simplifies formulation of typing rules for calculi that incorporate different modal axioms. These calculi have excellent computational properties, but each variant demands different, tedious and seemingly ad hoc treatment to prove meta-theoretic properties such as normalization. In this work, we identify the possible-world semantics of Fitch-style calculi and use it to develop normalization. The possible-world semantics enables a uniform treatment of Fitch-style calculi by isolating their differences to a specific parameter that identifies the modal fragment. 

### Papers & abstracts

* Normalization for Fitch-Style Modal Calculi ([pdf](https://nachivpn.me/nfmc.pdf))    
    ICFP 2022 (to appear)    
    Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas
  
* Semantic Analysis of Normalization by Evaluation for Fitch-Style Modal Calculi (extended abstract) ([pdf](https://nachivpn.me/types21.pdf), [video](https://www.youtube.com/watch?v=2OJBBWLYTQA))    
    [TYPES 2021](https://types21.liacs.nl/)        
    Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas

### Artifacts

* Agda mechanization ([github repo](https://github.com/nachivpn/k))
