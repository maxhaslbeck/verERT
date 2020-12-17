theory PGCL
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

inductive halt_free :: "'a pgcl \<Rightarrow> bool"
where
  Empty: "halt_free Empty"
| Skip: "halt_free Skip"
| Assign: "halt_free (Assign u)"
| Seq: "halt_free c\<^sub>1 \<Longrightarrow> halt_free c\<^sub>2 \<Longrightarrow> halt_free (Seq c\<^sub>1 c\<^sub>2)"
| Par: "halt_free c\<^sub>1 \<Longrightarrow> halt_free c\<^sub>2 \<Longrightarrow> halt_free (Par c\<^sub>1 c\<^sub>2)"
| If: "halt_free c\<^sub>1 \<Longrightarrow> halt_free c\<^sub>2 \<Longrightarrow> halt_free (If g c\<^sub>1 c\<^sub>2)"
| While: "halt_free c \<Longrightarrow> halt_free (While g c)"

inductive fully_probabilistic :: "'a pgcl \<Rightarrow> bool"
where
  Empty: "fully_probabilistic Empty"
| Skip: "fully_probabilistic Skip"
| Halt: "fully_probabilistic Halt"
| Assign: "fully_probabilistic (Assign u)"
| Seq: "fully_probabilistic c\<^sub>1 \<Longrightarrow> fully_probabilistic c\<^sub>2 \<Longrightarrow> fully_probabilistic (Seq c\<^sub>1 c\<^sub>2)"
| If: "fully_probabilistic c\<^sub>1 \<Longrightarrow> fully_probabilistic c\<^sub>2 \<Longrightarrow> fully_probabilistic (If g c\<^sub>1 c\<^sub>2)"
| While: "fully_probabilistic c \<Longrightarrow> fully_probabilistic (While g c)"

hide_fact (open) Empty Skip Halt Assign Seq If While

subsection \<open>Weakest Preexpectation Transformer\<close>

primrec wp :: "'a pgcl \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)"
where
  "wp Empty f = f"
| "wp Skip f = f"
| "wp Halt f = \<bottom>"
| "wp (Assign u) = (\<lambda>f x. \<integral>\<^sup>+y. f y \<partial>u x)"
| "wp (Seq c\<^sub>1 c\<^sub>2) f = wp c\<^sub>1 (wp c\<^sub>2 f)"
| "wp (Par c\<^sub>1 c\<^sub>2) f = wp c\<^sub>1 f \<sqinter> wp c\<^sub>2 f"
| "wp (If g c\<^sub>1 c\<^sub>2) f = (\<lambda>x. if g x then wp c\<^sub>1 f x else wp c\<^sub>2 f x)"
| "wp (While g c) f = lfp (\<lambda>W x. (if g x then wp c W x else f x))"

subsection \<open>Expected Runtime Transformer\<close>

primrec ert :: "'a pgcl \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)"
where
  "ert Empty f = f"
| "ert Skip f = 1 + f"
| "ert Halt f = 0"
| "ert (Assign u) f = 1 + (\<lambda>x. \<integral>\<^sup>+y. f y \<partial>u x)"
| "ert (Seq c\<^sub>1 c\<^sub>2) f = ert c\<^sub>1 (ert c\<^sub>2 f)"
| "ert (Par c\<^sub>1 c\<^sub>2) f = ert c\<^sub>1 f \<squnion> ert c\<^sub>2 f"
| "ert (If g c\<^sub>1 c\<^sub>2) f = 1 + (\<lambda>x. if g x then ert c\<^sub>1 f x else ert c\<^sub>2 f x)"
| "ert (While g c) f = lfp (\<lambda>W x. 1 + (if g x then ert c W x else f x))"

lemma sup_continuous_ert: "sup_continuous (ert P)"
  by (induction P)
     (auto intro!: order_continuous_intros sup_continuous_lfp''[THEN sup_continuous_applyD]
           dest: sup_continuous_compose sup_continuous_applyD)

lemma mono_ert: "mono (ert P)"
  using sup_continuous_mono[OF sup_continuous_ert] .

lemma ert_const_add:
  assumes P: "halt_free P"
  shows "ert P ((\<lambda>x. k) + f) = (\<lambda>x. k) + ert P f"
using P proof (induction arbitrary: f k)
  case Seq then show ?case by simp
next
  case (While c g f)
  have "(\<lambda>a. k) \<le> lfp (\<lambda>W x. 1 + (if g x then ert c W x else k + f x))"
  proof (intro lfp_greatest)
    fix u assume *: "(\<lambda>x. 1 + (if g x then ert c u x else k + f x)) \<le> u"
    have "(\<lambda>_. min k n) \<le> u" for n :: nat
    proof (induction n)
      case (Suc n)
      show ?case
      proof (rule le_funI)
        fix x
        show "min k (Suc n) \<le> u x"
        proof cases
          assume "g x"
          have "(\<lambda>_. min k (Suc n)) \<le> 1 + (\<lambda>_. min k n)"
            by (auto intro!: le_funI split: split_min
                     intro!: add_increasing ennreal_zero_less_one[THEN less_imp_le])
          also have "\<dots> \<le> 1 + ert c ((\<lambda>_. min k n) + 0)"
            by (subst While.IH) (intro add_left_mono order_refl zero_le add_increasing2)
          also have "\<dots> \<le> 1 + ert c u"
            by (auto intro: monoD[OF mono_ert] add_left_mono Suc)
          finally show ?thesis
            using \<open>g x\<close> *[THEN le_funD, of x] by (auto dest!: le_funD intro: order_trans)
        next
          assume "\<not> g x"
          have "min k (Suc n) \<le> k + (1 + f x)"
            by (intro min.coboundedI1 add_increasing2 zero_le) auto
          also have "\<dots> \<le> u x"
            using \<open>\<not> g x\<close> *[THEN le_funD, of x] by (auto simp: ac_simps)
          finally show ?thesis .
        qed
      qed
    qed (simp add: min.absorb2 zero_le le_funI)
    then have "(SUP n::nat. (\<lambda>_. min k n)) \<le> u"
      by (intro SUP_least)
    also have "(SUP n::nat. (\<lambda>_. min k n)) = (\<lambda>x. k)"
      by (auto intro!: antisym SUP_least le_funI simp: inf_min[symmetric] inf_SUP[symmetric] ennreal_SUP_of_nat_eq_top)
    finally show "(\<lambda>x. k) \<le> u" .
  qed

  with While show ?case
    apply simp
    apply (intro lfp_transfer[symmetric, where \<alpha>="\<lambda>f a. k + f a"])
    apply (auto intro!: order_continuous_intros sup_continuous_ert[THEN sup_continuous_applyD]
                        monoI[OF le_funI] add_mono mono_ert[THEN monoD, THEN le_funD]
                simp: fun_eq_iff add_ac bot_ennreal)
    done
qed (auto simp: sup_const_add_ennreal add_ac nn_integral_add)

lemma ert_infty: "halt_free P \<Longrightarrow> ert P \<top> = \<top>"
  using ert_const_add[of P \<top> 0] by (simp add: plus_fun_def top_add top_fun_def[symmetric])

lemma ert_subadditive: "ert P (F + G) \<le> ert P F + ert P G"
proof (induction P arbitrary: F G)
  case Empty then show ?case
    by simp
next
  case Skip then show ?case
    by (auto simp add: ac_simps le_fun_def add_increasing zero_le)
next
  case Halt then show ?case
    by (simp add: le_fun_def)
next
  case (Assign u f g) then show ?case
    by (auto simp: nn_integral_add intro!: le_funI)
next
  case (Seq c\<^sub>1 c\<^sub>2 F G)
  have "ert c\<^sub>1 (ert c\<^sub>2 (F + G)) \<le> ert c\<^sub>1 (ert c\<^sub>2 F + ert c\<^sub>2 G)"
    by (intro mono_ert[THEN monoD] Seq)
  also have "\<dots> \<le> ert c\<^sub>1 (ert c\<^sub>2 F) + ert c\<^sub>1 (ert c\<^sub>2 G)"
    by (intro Seq)
  finally show ?case
    by (simp del: plus_fun_apply)
next
  case (Par c\<^sub>1 c\<^sub>2 F G)
  have "ert c\<^sub>1 (F + G) \<squnion> ert c\<^sub>2 (F + G) \<le> (ert c\<^sub>1 F + ert c\<^sub>1 G) \<squnion> (ert c\<^sub>2 F + ert c\<^sub>2 G)"
    by (intro sup.mono Par)
  also have "\<dots> \<le> (ert c\<^sub>1 F \<squnion> ert c\<^sub>2 F) + (ert c\<^sub>1 G \<squnion> ert c\<^sub>2 G)"
    by (intro sup_least add_mono) auto
  finally show ?case
    by (simp del: plus_fun_apply sup_apply)
next
  case (If g c\<^sub>1 c\<^sub>2 F G) then show ?case
    by (auto simp: le_fun_def ac_simps intro!: add_increasing[of 1 _ _])
next
  case (While g c F G)
  let ?P = "\<lambda>F W x. 1 + (if g x then ert c W x else F x)"
  have *: "\<And>F. mono (?P F)"
    by (auto simp: mono_def le_fun_def intro!: add_mono mono_ert[THEN monoD, THEN le_funD])

  have "?P (\<lambda>x. F x + G x) (lfp (?P F) + lfp (?P G)) \<le> ?P F (lfp (?P F)) + ?P G (lfp (?P G))"
    using add_left_mono[OF While, of 1, THEN le_funD]
    by (auto intro!: add_increasing[of 1 _ _] simp: ac_simps le_fun_def plus_fun_def)
  also have "\<dots> = lfp (?P F) + lfp (?P G)"
    unfolding lfp_unfold[OF *, symmetric] ..
  finally show ?case
    by (clarsimp intro!: lfp_lowerbound simp add: plus_fun_def cong: if_cong)
qed

end