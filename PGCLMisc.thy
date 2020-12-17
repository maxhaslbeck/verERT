\<^marker>\<open>creator "Johannes Hölzl"\<close>
\<^marker>\<open>contributor "Maximilian P.L. Haslbeck"\<close>
theory PGCLMisc
imports MDP_Semantics
begin



subsection "Johannes"


lemma lfp_linear:
  assumes "b < 1"
  shows "lfp (\<lambda>r. a + b * r :: ennreal) = a / (1 - b)"
proof (rule antisym)
  show "lfp (\<lambda>r. a + b * r) \<le> a / (1 - b)"
  proof (intro lfp_lowerbound)
    show "a + b * (a / (1 - b)) \<le> a / (1 - b)"
      using \<open>b < 1\<close>
      by (cases a b rule: ennreal2_cases)
         (auto simp del: ennreal_1 ennreal_plus
               simp add: ennreal_1[symmetric] ennreal_mult[symmetric] ennreal_plus[symmetric]
                         ennreal_minus divide_ennreal ennreal_less_iff field_simps ennreal_top_divide)
  qed
  show "a / (1 - b) \<le> lfp (\<lambda>r. a + b * r)"
  proof (rule lfp_greatest)
    fix u show "a + b * u \<le> u \<Longrightarrow> a / (1 - b) \<le> u"
      using \<open>b < 1\<close>
      by (cases a b u rule: ennreal3_cases)
         (auto simp del: ennreal_1 ennreal_plus
               simp add: ennreal_1[symmetric] ennreal_mult[symmetric] ennreal_plus[symmetric]
                         ennreal_minus divide_ennreal ennreal_less_iff field_simps top_add top_unique)
  qed
qed


lemma lfp_linear_inf:
  assumes "b \<ge> 1" and "a > 0"
  shows "lfp (\<lambda>r. a + b * r :: ennreal) = \<infinity>"
proof (rule antisym)
  show "lfp (\<lambda>r. a + b * r :: ennreal) \<ge> \<infinity>"
  proof (rule lfp_greatest)
    fix u show "a + b * u \<le> u \<Longrightarrow> \<infinity> \<le> u"
      using \<open>b \<ge> 1\<close>  \<open>a > 0\<close>
      apply (cases a b u rule: ennreal3_cases)
      apply 
           (auto simp del: ennreal_1 ennreal_plus
                 simp add: ennreal_1[symmetric] ennreal_mult[symmetric] ennreal_plus[symmetric]
                           ennreal_minus divide_ennreal ennreal_less_iff field_simps top_add top_unique)
      subgoal for a' b' u' using mult_right_mono by fastforce
      subgoal for a' u'
        by (metis add.right_neutral assms(2) ennreal_add_eq_top ennreal_neq_top ennreal_top_mult le_zero_eq not_gr_zero top.extremum_unique)
      done
  qed
  show "lfp (\<lambda>r. a + b * r :: ennreal) \<le> \<infinity>" by auto
qed


lemma lfp_parallel_induct[consumes 2, case_names bot step cont]:
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  assumes bot: "R \<bottom> \<bottom>"
  assumes step: "\<And>x y. R x y \<Longrightarrow> R (f x) (g y)"
  assumes cont: "\<And>X Y. (\<And>i::nat. R (X i) (Y i)) \<Longrightarrow> mono X \<Longrightarrow> mono Y \<Longrightarrow> R (SUP i. X i) (SUP i. Y i)"
  shows "R (lfp f) (lfp g)"
  unfolding f[THEN sup_continuous_lfp] g[THEN sup_continuous_lfp]
proof (rule cont)
  show "incseq (\<lambda>i. (f ^^ i) \<bottom>)" "incseq (\<lambda>i. (g ^^ i) \<bottom>)"
    by (intro mono_funpow f[THEN sup_continuous_mono] g[THEN sup_continuous_mono])+
  show "R ((f ^^ i) \<bottom>) ((g ^^ i) \<bottom>)" for i
    by (induction i) (auto intro: bot step)
qed



subsection "misc"


lemma sup_continuous_wp: "sup_continuous (wp P)"
  by (induction P)         
     (auto intro!: order_continuous_intros sup_continuous_lfp''[THEN sup_continuous_applyD]
           dest: sup_continuous_compose sup_continuous_applyD)

lemma mono_wp: "mono (wp P)"
  using sup_continuous_mono[OF sup_continuous_wp] . 


subsection \<open>Angelic Weakest Preexpectation Transformer\<close>

primrec awp :: "'a pgcl \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ('a \<Rightarrow> ennreal)"
where
  "awp Empty f = f"
| "awp Skip f = f"
| "awp Halt f = \<bottom>"
| "awp (Assign u) = (\<lambda>f x. \<integral>\<^sup>+y. f y \<partial>u x)"
| "awp (Seq c\<^sub>1 c\<^sub>2) f = awp c\<^sub>1 (awp c\<^sub>2 f)"
| "awp (Par c\<^sub>1 c\<^sub>2) f = (awp c\<^sub>1 f) \<squnion> (awp c\<^sub>2 f)"
| "awp (If g c\<^sub>1 c\<^sub>2) f = (\<lambda>x. if g x then awp c\<^sub>1 f x else awp c\<^sub>2 f x)"
| "awp (While g c) f = lfp (\<lambda>W x. (if g x then awp c W x else f x))"

lemma sup_continuous_awp: "sup_continuous (awp P)"
  by (induction P)      
     (auto intro!: order_continuous_intros sup_continuous_lfp''[THEN sup_continuous_applyD]
           dest: sup_continuous_compose sup_continuous_applyD)   

lemma mono_awp: "mono (awp P)"
  using sup_continuous_mono[OF sup_continuous_awp] . 



end