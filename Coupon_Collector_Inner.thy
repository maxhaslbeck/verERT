\<^marker>\<open>creator "Maximilian P.L. Haslbeck"\<close>
section "Analysis of the inner loop of the Coupon Collector Example"
theory Coupon_Collector_Inner
imports ERT_Of_IID_Loop
begin


paragraph \<open>Summary\<close>

text \<open>This theory formalizes the new proof rules for ert of f-iid loops and generalizes the
      result to angelic weakest preexpectation.
      The first result is Theorem 4 of @{cite batzESOP18}
    \<close>



 
lemma ennreal_divide_distrib: "(a + b::ennreal) / c = a / c + b / c"
  by (simp add: field_simps divide_ennreal_def)


definition "innerb (N::nat) = (WHILE (%s. s ''b'' \<noteq> 1) DO
        Assign ''b'' (%s. map_pmf (\<lambda>b. if b then 0 else 1)
                         (bernoulli_pmf (real (s ''a'') / N))))"



definition "coco N = Assign ''b'' (\<lambda>s. return_pmf (0)) ;;
                     Assign ''a'' (\<lambda>s. return_pmf (1)) ;;
                     innerb N"


subsection "Semantic Approach"

lemma fixes N::nat
  assumes N: "N>1"
  shows "ert (compile (coco N)) 0 s = 3 +  (2 * real N / (real N - 1))"
proof -
  { fix s :: state and W :: exp
    assume   a: "s ''a'' < N" and "s ''a'' \<ge> 0" and b: "s ''b'' = 1 \<or> s ''b'' = 0"
    then obtain i where ai: "s ''a'' = i"
      using nonneg_int_cases by blast 
    with a have "i<N" by simp
    let ?f = "\<lambda>W' s. 1 + (if s ''b'' \<noteq> 1 then W' s else W s)"
    let ?g = "\<lambda>W' s. 1 + \<integral>\<^sup>+ b. W' (s(''b'':=(if b then 0 else 1))) \<partial>bernoulli_pmf (real (s ''a'') / N)"
    let ?r = "\<lambda>i s r::ennreal. (2 + (W (s(''b'':=1)) * (1 - real i / N))) + (real i / N) * r"
    have *: "sup_continuous (\<lambda>x. ?g (?f x))" "sup_continuous (?r i s)" for i :: nat and s :: state
      by (auto intro!: order_continuous_intros)
    have eq: "lfp (\<lambda>x. ?f (?g x)) = ?f (lfp (\<lambda>x. ?g (?f x)))"
      by (rule lfp_rolling[where g="?f", symmetric])
         (auto simp: mono_def le_fun_def intro!: nn_integral_mono)
    have i: "\<And>s x. s ''b'' = x \<Longrightarrow> (s(''b'' := x)) = s" by auto
    { fix s'::state and i assume "i < N" and x: "s' ''a'' = i" "s' ''b'' \<noteq> 1"  and b: "s' ''b'' = 1 \<or> s' ''b'' = 0"
      have "lfp (\<lambda>x. ?g (?f x)) s' = lfp (?r i s')"
        using * x b
      proof (induction rule: lfp_parallel_induct)
        case (step a b)
        then have k: "s' ''b'' = 0" by auto
        then have z: "s'(''b'' := 0) = s'" by auto
          from step(1,2) k z  \<open>i < N\<close> show ?case
          apply (subst nn_integral_add)
            apply simp_all          
            apply (simp add:   field_simps one_add_one[symmetric] del: one_add_one)   
          done
      qed (auto simp: SUP_image)
      also have "\<dots> = (2 + (W (s'(''b'':=1))) * (1 - real i / real N)) / (1 - real i / real N)"
        using \<open>i < N\<close>
        apply (subst lfp_linear)
        by (simp_all add: ennreal_minus[symmetric])
      also have "\<dots> = 2 / (1 - real i / real N) + W (s'(''b'':=1))"
        using \<open>i < N\<close>
        apply (subst ennreal_divide_distrib)
        by (simp add: divide_ennreal[symmetric] ennreal_mult_divide_eq)
      also have "2 / (1 - real i / real N) = 2 * real N / (N - i)"
        using \<open>i < N\<close> by (simp add: field_simps)
      finally have "lfp (\<lambda>x. ?g (?f x)) s' = 2 * real N / (N - i) + W (s'(''b'':=1))"
        . } note t=this
    have " lfp (\<lambda>Wa s. 1 + (if s ''b'' \<noteq> 1 then (1 + (\<lambda>x. \<integral>\<^sup>+ xa. Wa (x(''b'' := if xa then 0 else 1)) \<partial>measure_pmf (bernoulli_pmf (real (x ''a'') / real N)))) s else W s)) s
          = lfp (\<lambda>x. ?f (?g x)) s"
      by (metis (no_types, lifting) one_fun_apply plus_fun_apply) 
    also from t[of i s, OF \<open>i < N\<close> ai _ b] have "\<dots> = (if s ''b'' \<noteq> 1 then 1 + 2 * (real N / (N - i) ) else 1) + W (s(''b'':=1))"
      unfolding eq apply auto apply(subst i) by auto
    also have "real (N - i) = real_of_int (int N - s ''a'')"
      using \<open>i < N\<close> ai by auto
    finally have " lfp (\<lambda>Wa s. 1 + (if s ''b'' \<noteq> 1 then (1 + (\<lambda>x. \<integral>\<^sup>+ xa. Wa (x(''b'' := if xa then 0 else 1)) \<partial>measure_pmf (bernoulli_pmf (real (x ''a'') / real N)))) s else W s)) s =
  ennreal (if s ''b'' \<noteq> 1 then 1 + 2 * (real N / real_of_int (int N - s ''a'')) else 1) + W (s(''b'' := 1))"
      .
    }
    note inner = this
    {
      fix s:: state and f :: exp
      have "0 \<le> s ''a'' \<Longrightarrow> s ''a'' <N \<Longrightarrow> s ''b'' = 0 \<or> s ''b'' = 1
           \<Longrightarrow>  ert (compile (innerb N)) f s =
              (if s ''b'' \<noteq> 1 then 1 + 2 * (real N / real (N - s ''a'')) else 1) + f (s(''b'' := 1))"
        unfolding innerb_def apply (simp only: map_pmf_comp ert.simps compile.simps) 
        apply(subst nn_integral_map_pmf) apply(subst inner)
        by auto
    } note l=this
  
    from assms show ?thesis  unfolding coco_def
      apply auto apply(subst l) apply auto
      apply(auto simp only: ennreal_numeral[symmetric] ennreal_1[symmetric]  )           
      apply(subst ennreal_plus[symmetric]) apply auto[2]
      apply(subst ennreal_plus[symmetric]) apply auto[2]
      apply(subst ennreal_plus[symmetric]) apply auto[2]
      apply(subst ennreal_plus[symmetric]) apply auto[2]
      by simp
  qed

 
subsection "Using the Prove Rule for f-iid Loops" 
 
lemma fixes N::nat
  assumes N: "N>1"
  shows "ert (compile (coco N)) 0 s = 3 +  (2 * real N / (real N - 1))"
proof -
    
  { 
    fix s :: state assume a: "s ''b'' = 0" "s ''a''=1" "s ''b'' = 0 \<or> s ''b''=1"
    have "ert (compile (innerb N)) 0 s = 1 + 2 / (1 - ennreal (1 / real N))"
      unfolding innerb_def
      apply(subst prove_rule)
      using a N 
      by (auto simp: fiid_def unaffected_def Vars_def lift2_def)  
  } note k=this
 
  from N have *: "1 - 1 / real N = (real N - 1) / real N"
    by(simp add: diff_divide_distrib) 
  have l: "(2::ennreal) = ennreal 2" by auto
  have eq: "2 / (1 - ennreal (1 / real N))
        =  ennreal (2 * real N / (real N - 1))"
    apply(subst ennreal_1[symmetric]) apply(subst ennreal_minus)
    using N   apply(auto simp add: divide_ennreal)
    unfolding l apply(subst divide_ennreal) apply auto 
    unfolding *
    apply(subst divide_divide_eq_right) by simp

  show ?thesis unfolding coco_def apply auto
    apply(subst k) using N apply auto using eq by auto
qed

  




end