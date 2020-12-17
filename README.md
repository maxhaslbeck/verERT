# Verified expected running time of probabilistic programs

This repository verifies the analysis of expected running time of probabilistic programs in Isabelle/HOL.

The main contents are

- Formalized ERT calculus (following [3])
- A new proof rule for ERT of f-iid loops (following [4])
- A probabilistic quantitative Hoare Logic (following [5])


### Formalized ERT calculus

For this we formalized the expected running time of PGCL as defined in [1]. The
formalization is in PGCL.thy

Currently it mainly consists of an equivalence proof between the denotational
expectation running transformer semantics and an operational interpretation of
pGCL running times as MDPs (in [MDP_Semantics.thy]). The proof is based on the
definitions of Kaminski et al [1]. The proof itself is different, it follows
the equivalence proof in [2], where we use least fixed-points and transfer
rules on them.

In [Random_Walk.thy] we prove that the expected running time of an symmetric
simple random walk is actually infinite.
In [Coupon_Collector.thy] we prove the expected running time of the coupon collector
problem.

This work is described in the the ITP'16 paper [3].

[1] Weakest Precondition Reasoning for Expected Run-Times of Probabilistic Programs -- Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo
[http://arxiv.org/abs/1601.01001] (full version of the ESOP 2016 paper)

[2] Markov chains and Markov decision processes in Isabelle/HOL -- Johannes Hölzl
[https://link.springer.com/article/10.1007/s10817-016-9401-5]

[3] Formalising Semantics for Expected Running Time of Probabilistic Programs (Rough Diamond)
    Johannes Hölzl
    [https://link.springer.com/chapter/10.1007/978-3-319-43144-4_30]


### A new proof rule for ERT of f-iid loops

We prove the rule for ERT of f-iid loops (Theorem 4 in [4]) and generalize it to
angelic weakest preexpectation (in [ERT_Of_IID_Loop.thy]).

We use it shorten the analysis of the inner loop of the coupon collector problem
considerabley: see [Coupon_Collector_Inner.thy]. 

[4] How long, O Bayesian network, will I sample thee? --
Kevin Batz, Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja
  [https://link.springer.com/chapter/10.1007/978-3-319-89884-1_7]

### A probabilistic quantitative Hoare Logic

We generalize the quantitative Hoare Logic by Carbonneaux to handle the expected
running time of probabilistic programs. We follow the paper by Ngo et al [5] only
restricted to programs *without* procedures. We prove soundness *and* completeness
of the calculus. Also we provide a VCG and prove it sound and complete. ([Probabilistic_Quantitative_Hoare_Logic]).
This is a astonishingly straightward extension of the quantitative Hoare Logic which
we verified in [an AFP entry](https://www.isa-afp.org/browser_info/current/AFP/Hoare_Time/Quant_Hoare.html).


[5] Bounded expectations: resource analysis for probabilistic programs --
Van Chan Ngo, Quentin Carbonneaux, Jan Hoffmann
[https://dl.acm.org/doi/abs/10.1145/3296979.3192394]
  
