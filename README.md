This is the start of an average running time analysis in Isabelle/HOL.

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

[1] Weakest Precondition Reasoning for Expected Run-Times of Probabilistic Programs
    Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo
    http://arxiv.org/abs/1601.01001 (full version of the ESOP 2016 paper)

[2] Markov chains and Markov decision processes in Isabelle/HOL
    Johannes Hölzl
    http://home.in.tum.de/~hoelzl/mdptheory/

