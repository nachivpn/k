## Fitch-Style Modal Calculi

In type systems, a modality can be broadly construed as a unary type constructor with certain properties. Type systems with modalities have found a wide range of applications in programming languages to capture and specify properties of a program in its type. In this work, we study typed lambda calculi equipped with a necessity modality (denoted by ☐) formulated in the so-called Fitch style. The necessity modality, which originates from modal logic, has found applications in modelling purity in an impure functional language, confidentiality in information-flow control, and binding-time separation in partial evaluation and staged computation.

Different applications may demand different modal operations, and the Fitch-style technique provides us with a uniform recipe to design modal calculi. Fitch-style modal calculi feature necessity modalities in a lambda calculus by extending the typing context with a delimiting &quot;lock&quot; operator (denoted by 🔒). The characteristic lock operator simplifies formulating calculi that incorporate different modal operations and these calculi have excellent computational properties. Each variant demands, however, different, tedious and seemingly ad hoc treatment to prove meta-theoretic properties such as normalization. In this project, we identify the possible-world semantics of Fitch-style calculi and use it to develop normalization. The possible-world semantics enables a uniform treatment of various Fitch-style calculi by isolating their differences to a specific parameter that identifies the modal fragment. We showcase several consequences of normalization for proving meta-theoretic properties of Fitch-style calculi based on different interpretations of the necessity modality in programming languages, such as capability safety, noninterference and a form of binding-time correctness.

### Papers & Abstracts

* Fitch-Style Applicative Functors (Extended Abstract)  
  Draft 2023  
  Nachiappan Valliappan, Fabian Ruch  
  Article: [Authors' version](https://nachivpn.me/r.pdf)  
* Normalization for Fitch-Style Modal Calculi  
  [ICFP 2022](https://icfp22.sigplan.org/) (<span style="color:IndianRed">Distinguished paper award</span>)  
  Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas  
  Article: [Authors' version](https://nachivpn.me/nfmc.pdf), [arXiv](https://doi.org/10.48550/arXiv.2207.12807), [PACMPL](https://doi.org/10.1145/3547649); Talk video: [YouTube](https://youtu.be/f8U47q8dARI)  
* Semantic Analysis of Normalization by Evaluation for Fitch-Style Modal Calculi (extended abstract)  
  [TYPES 2021](https://types21.liacs.nl/)  
  Nachiappan Valliappan, Fabian Ruch, Carlos Tomé Cortiñas  
  Article: [Authors' version](https://nachivpn.me/types21.pdf); Talk video: [YouTube](https://www.youtube.com/watch?v=2OJBBWLYTQA)

### Artifacts

* Agda mechanization  
  Source: [Browseable code](html/Everything.html), [GitHub repo](https://github.com/nachivpn/k)
