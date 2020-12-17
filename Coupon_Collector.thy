theory Coupon_Collector
  imports PGCL
begin

lemma setsum_bool:
  fixes f :: "bool \<Rightarrow> 'a::semiring_1"
  assumes [simp]: "finite F"
  shows "(\<Sum>i\<in>F. f (P i)) = of_nat (card {x\<in>F. P x}) * f True + of_nat (card {x\<in>F. \<not> P x}) * f False"
proof -
  have "(\<Sum>i\<in>F. f (P i)) = (\<Sum>i\<in>F. if P i then f True else f False)"
    by (intro sum.cong) auto
  also have "\<dots> = of_nat (card {x\<in>F. P x}) * f True + of_nat (card {x\<in>F. \<not> P x}) * f False"
    by (simp add: sum.If_cases Int_def)
  finally show ?thesis .
qed

lemma lfp_mult: "lfp (\<lambda>r. a * r :: ennreal) = 0"
proof -
  have "lfp (\<lambda>r. a * r) \<le> 0"
    by (intro lfp_lowerbound) simp
  then show ?thesis
    by simp
qed

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

lemma ennreal_divide_distrib: "(a + b::ennreal) / c = a / c + b / c"
  by (simp add: field_simps divide_ennreal_def)

text \<open>
  The following lemma can also be stated using monotone functions @{term f} and  @{term g}. But then
  the continuity assumption needs to be for all cardinals, not only countable.
\<close>

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

definition DetAssign :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a pgcl"
where
  "DetAssign f = Assign (\<lambda>s. return_pmf (f s))"

lemma ert_DetAssign[simp]: "ert (DetAssign f) g = 1 + (\<lambda>x. g (f x))"
  by (simp add: DetAssign_def)

record coupon_collector =
  cp :: "nat \<Rightarrow> bool"
  x :: nat
  i :: nat


definition cc :: "nat \<Rightarrow> coupon_collector pgcl"
where
  "cc N =
    DetAssign (\<lambda>_. \<lparr> cp = \<lambda>_. False, x = 0, i = 0 \<rparr>) ;;
    WHILE (\<lambda>s. x s < N) DO
      (WHILE (\<lambda>s. cp s (i s)) DO
        Assign (\<lambda>s. map_pmf (\<lambda>i'. s\<lparr> i := i' \<rparr>) (pmf_of_set {0 ..< N})) ;;
      DetAssign (\<lambda>s. s\<lparr> cp := (cp s)(i s := True)\<rparr>) ;;
      DetAssign (\<lambda>s. s\<lparr> x := x s + 1 \<rparr>))"

lemma ert_cc:
  fixes N :: nat
  assumes "0 < N"
  shows "ert (cc N) \<bottom> = (\<lambda>_. ennreal (2 + N * 4 + 2 * N * (\<Sum>i<N - 1. 1 / Suc i)))"
proof -
  define C :: "(nat \<Rightarrow> bool) \<Rightarrow> nat"
  where "C P = card {i. P i}" for P

  define cc_body :: "coupon_collector pgcl"
  where
    "cc_body =
      (WHILE (\<lambda>s. cp s (i s)) DO
        Assign (\<lambda>s. map_pmf (\<lambda>i'. s\<lparr> i := i' \<rparr>) (pmf_of_set {0 ..< N})) ;;
      DetAssign (\<lambda>s. s\<lparr> cp := (cp s)(i s := True)\<rparr>) ;;
      DetAssign (\<lambda>s. s\<lparr> x := x s + 1 \<rparr>))"

  define cc'_body :: "(nat \<times> bool) pgcl"
  where
    "cc'_body =
      (WHILE snd DO
        Assign (\<lambda>s. map_pmf (\<lambda>b. (fst s, b)) (bernoulli_pmf (real (fst s) / N))) ;;
      DetAssign (\<lambda>s. (fst s, True)) ;;
      DetAssign (\<lambda>s. (Suc (fst s), True)))"

  define cc' :: "(nat \<times> bool) pgcl"
  where
    "cc' = DetAssign (\<lambda>_. (0, False)) ;; WHILE (\<lambda>s. fst s < N) DO cc'_body"

  have "sup_continuous (\<lambda>W s. 1 + (if x s < N then ert cc_body W s else \<bottom> s))"
      "sup_continuous (\<lambda>W x. 1 + (if fst x < N then ert cc'_body W x else \<bottom> x))"
    by (auto intro!: order_continuous_intros sup_continuous_ert[THEN sup_continuous_applyD])
  then have eq1:
    "\<And>s. x s = C (cp s) \<Longrightarrow> i s < N \<Longrightarrow> {i. cp s i} \<subseteq> {0..< N} \<Longrightarrow>
      lfp (\<lambda>W s. 1 + (if x s < N then ert cc_body W s else \<bottom> s)) s =
      lfp (\<lambda>W x. 1 + (if fst x < N then ert cc'_body W x else \<bottom> x)) (x s, cp s (i s))"
  proof (induction rule: lfp_parallel_induct)
    case outer: (step f f')
    let ?B = "(\<lambda>W xa. 1 + (if cp xa (i xa)
      then ert (Assign (\<lambda>s. map_pmf (\<lambda>i'. s\<lparr>i := i'\<rparr>) (pmf_of_set {0..<N}))) W xa
      else (1 + (\<lambda>xa. 1 + f (xa\<lparr>cp := (cp xa)(i xa := True), x := Suc (x xa)\<rparr>))) xa))"
    let ?B' = "(\<lambda>W x. 1 + (if snd x
      then ert (Assign (\<lambda>s. map_pmf (Pair (fst s)) (bernoulli_pmf (real (fst s) / real N)))) W x
      else (1 + (\<lambda>x. 1 + f' (Suc (fst x), True))) x))"
    have "sup_continuous ?B" "sup_continuous ?B'"
      by (auto intro!: order_continuous_intros sup_continuous_ert[THEN sup_continuous_applyD])
    then have "x s = C (cp s) \<Longrightarrow> i s < N \<Longrightarrow> {i. cp s i} \<subseteq> {0..< N} \<Longrightarrow> lfp ?B s = lfp ?B' (C (cp s), cp s (i s))"
    proof (induction arbitrary: s rule: lfp_parallel_induct)
      case (step g g' s')
      moreover have "C (cp s') \<le> N"
        using card_mono[OF _ step.prems(3)] by (auto simp: C_def)
      moreover
      have eq: "{x. x < N \<and> cp s' x} = {x. cp s' x}" "{x. x < N \<and> \<not> cp s' x} = {0..< N} - {x. cp s' x}"
        using step.prems(3) by auto
      have "card {x. x < N \<and> cp s' x} = C (cp s')" "card {x. x < N \<and> \<not> cp s' x} = N - C (cp s')"
        unfolding eq C_def using step.prems(3)
        by (simp_all add: card_Diff_subset finite_subset)
      moreover
      have "{ia. ia \<noteq> i s' \<longrightarrow> cp s' ia} = insert (i s') {x. cp s' x}"
        by auto
      ultimately show ?case
        using \<open>0 < N\<close>
        apply (auto simp: nn_integral_pmf_of_set)
        apply (subst setsum_bool)
        apply simp
        apply (simp add: mult.commute[of _ "g' _"] ennreal_divide_distrib divide_ennreal ennreal_of_nat_eq_real_of_nat
          of_nat_diff ennreal_times_divide[symmetric] divide_simps)
        apply (auto simp add: C_def card_insert_if finite_subset outer)
        done
    qed auto
    with outer show ?case
      by (auto simp: cc_body_def cc'_body_def)
  qed auto

  { fix W :: "nat \<times> bool \<Rightarrow> ennreal" and x :: "nat \<times> bool" assume "fst x < N"
    let ?f = "\<lambda>W' x. 1 + (if snd x then W' x else 1 + (1 + W (Suc (fst x), True)))"
    let ?g = "\<lambda>W' x. 1 + \<integral>\<^sup>+ b. W' (fst x, b) \<partial>bernoulli_pmf (real (fst x) / N)"
    let ?r = "\<lambda>i r::ennreal. (2 + (2 + W (Suc i, True)) * (1 - real i / N)) + (real i / N) * r"
    have *: "sup_continuous (\<lambda>x. ?g (?f x))" "sup_continuous (?r i)" for i :: nat
      by (auto intro!: order_continuous_intros)
    have eq: "lfp (\<lambda>x. ?f (?g x)) = ?f (lfp (\<lambda>x. ?g (?f x)))"
      by (rule lfp_rolling[where g="?f", symmetric])
         (auto simp: mono_def le_fun_def intro!: nn_integral_mono)
    { fix x i assume "i < N" and x: "fst x = i" "snd x"
      have "lfp (\<lambda>x. ?g (?f x)) x = lfp (?r i)"
        using * x
      proof (induction rule: lfp_parallel_induct)
        case (step a b) with \<open>i < N\<close> show ?case
          apply (subst nn_integral_add)
          apply simp_all
          apply (cases x)
          apply (simp add: field_simps one_add_one[symmetric] del: one_add_one)
          done
      qed auto
      also have "\<dots> = (2 + (2 + W (Suc i, True)) * (1 - real i / N)) / (1 - real i / real N)"
        using \<open>i < N\<close> by (subst lfp_linear) (simp_all add: ennreal_minus[symmetric])
      also have "\<dots> = 2 / (1 - real i / real N) + 2 + W (Suc i, True)"
        using \<open>i < N\<close>
        by (subst ennreal_divide_distrib) (simp add: divide_ennreal[symmetric] ennreal_mult_divide_eq)
      also have "2 / (1 - real i / real N) = 2 * real N / (N - i)"
        using \<open>i < N\<close> by (simp add: field_simps)
      finally have "lfp (\<lambda>x. ?g (?f x)) x = 2 * (real N / (N - i) + 1) + W (Suc i, True)"
        by (simp add: field_simps) }
    from this[of "fst x" x]
    have "lfp (\<lambda>x. ?f (?g x)) x = (if snd x then 1 + 2 * (real N / (N - fst x) + 1) else 3) + W (Suc (fst x), True)"
      unfolding eq using \<open>fst x < N\<close> by simp }
  note inner = this

  define outer where
    "outer F x = 1 + (if Suc x < N then 3 + ennreal (2 * real N / real (N - Suc x)) + F (Suc x) else 0)" for F x

  have "mono outer"
    by (auto simp: mono_def le_fun_def outer_def)
  { fix i assume "i < N"
    then have "lfp outer (N - Suc i) = (\<Sum>j=0..<i. 4 + 2 * N / Suc j) + 1"
    proof (induction i)
      case 0 with \<open>0 < N\<close> show ?case
        by (rewrite lfp_unfold[OF \<open>mono outer\<close>]) (simp add: outer_def)
    next
      case (Suc i) with \<open>0 < N\<close> show ?case
        apply (rewrite lfp_unfold[OF \<open>mono outer\<close>])
        apply (rewrite outer_def)
        apply (simp add: Suc_diff_Suc ac_simps sum_nonneg)
        done
    qed }
  from this[of "N - 1"] \<open>0 < N\<close> have outer: "lfp outer 0 = 4 * (N - 1) + 2 * N * (\<Sum>j=0..<N - 1. 1 / Suc j) + 1"
    by (auto intro!: arg_cong[where f=ennreal] simp: sum_distrib_left sum.distrib)

  { fix s
    have "ert (cc N) \<bottom> s = ert cc' \<bottom> undefined"
      unfolding cc_def cc'_def cc_body_def[symmetric] using \<open>0 < N\<close> by (simp add: eq1 C_def)
    also have "\<dots> = ennreal (6 + (N - 1) * 4 + 2 * N * (\<Sum>i<N - 1. 1 / Suc i))"
      using \<open>0 < N\<close>
      apply (simp add: cc'_def cc'_body_def inner cong: if_cong)
      apply (subst lfp_rolling[symmetric, where f="\<lambda>W x. W (Suc x, True)"])
      apply (auto simp: mono_def le_fun_def bot_ennreal outer_def[symmetric] outer
                  cong: if_cong)
      apply (simp add: ac_simps sum_nonneg atLeast0LessThan)
      done
    also have "\<dots> = ennreal (2 + N * 4 + 2 * N * (\<Sum>i<N - 1. 1 / Suc i))"
      using \<open>0 < N\<close> by (intro arg_cong[where f=ennreal]) (auto simp add: field_simps)
    finally have "ert (cc N) \<bottom> s = ennreal (2 + N * 4 + 2 * N * (\<Sum>i<N - 1. 1 / Suc i))" . }
  then show ?thesis
   by (simp add: fun_eq_iff)
qed

end
