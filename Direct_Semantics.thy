theory Direct_Semantics
  imports Misc
begin

section \<open>Probabilistic Guarded Command Language\<close>

datatype 'a pgcl = Empty
                 | Skip
                 | Halt
                 | Assign "'a \<Rightarrow> 'a pmf"
                 | Seq (left: "'a pgcl") (right: "'a pgcl") ("_;;/ _"  [60, 61] 60)
                 | Par (left: "'a pgcl") (right: "'a pgcl")
                 | If "'a \<Rightarrow> bool" (left: "'a pgcl") (right: "'a pgcl")
                 | While "'a \<Rightarrow> bool" "'a pgcl" ("(WHILE _/ DO _)"  [0, 61] 61)

subsection \<open>Weakest Preexpectation Transformer\<close>

primrec wp :: "'a pgcl \<Rightarrow> ('a \<Rightarrow> 'a pmf) set"
where
  "wp Empty = { return_pmf }"
| "wp Skip = { return_pmf }"
| "wp Halt = {}"
| "wp (Assign u) = { u }"
| "wp (Seq c\<^sub>1 c\<^sub>2) = (\<Union>I1\<in>wp c\<^sub>1. \<Union>I2\<in>wp c\<^sub>2. { \<lambda>s. bind_pmf (I1 s) I2 })"
| "wp (Par c\<^sub>1 c\<^sub>2) = wp c\<^sub>1 \<union> wp c\<^sub>2"
| "wp (If g c\<^sub>1 c\<^sub>2) = (\<Union>I1\<in>wp c\<^sub>1. \<Union>I2\<in>wp c\<^sub>2. { \<lambda>s. if g s then I1 s else I2 s })"
| "wp (While g c) = {}"
