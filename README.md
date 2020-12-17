# Verified expected running time of probabilistic programs

This repository verifies the analysis of expected running time of probabilistic programs in Isabelle/HOL.

## Formalized ERT calculus

For this we formalized the expected running time of PGCL as defined in [1]. The
formalization is in PGCL.thy

Currently it mainly consists of an equivalence proof between the denotational
expectation running transformer semantics and an operational interpretation of
pGCL running times asas MDPs (in MDP_Semantics.thy). The proof is based on the
definitions of Kaminski et al [1]. The proof itself is different, it follows
the equivalence proof in [2], where we use least fixed-points and transfer
rules on them.

In Random_Walk.thy we prove that the expected running time of an symmetric
simple random walk is actually infinite.

This work is described in the the ITP'16 paper [3].

[1] Weakest Precondition Reasoning for Expected Run-Times of Probabilistic Programs
    Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo
    [http://arxiv.org/abs/1601.01001] (full version of the ESOP 2016 paper)

[2] Markov chains and Markov decision processes in Isabelle/HOL
    Johannes Hölzl
    [https://link.springer.com/article/10.1007/s10817-016-9401-5]

[3] Formalising Semantics for Expected Running Time of Probabilistic Programs (Rough Diamond)
    Johannes Hölzl
    [https://link.springer.com/chapter/10.1007/978-3-319-43144-4_30]
