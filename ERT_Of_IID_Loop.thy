\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
chapter "New Prove Rule for iid loops"
theory ERT_Of_IID_Loop
imports PGCL_With_State IID_Loops
begin

paragraph \<open>Summary\<close>

text \<open>This theory formalizes the new proof rules for ert of f-iid loops and generalizes the
      result to angelic weakest preexpectation.
      The first result is Theorem 4 of @{cite batzESOP18}
    \<close>

paragraph \<open>Main Lemmas\<close>

text \<open>
  \<^item> prove_rule: proof rule for ert = Theorem 4 of @{cite batzESOP18}
  \<^item> prove_rule_awp: generalization of the proof rule to non-deterministic programs
\<close>

 
section \<open>New Prove Rule for deterministic case\<close>


lemma 
  assumes [simp]: "deter C" "unaffected x C"
    and wp1: "wp (compile C) 1 = 1"
shows deter_decompose: "ert (compile C) (1  + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))
            = 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + wp (compile C) (\<lbrakk>b\<rbrakk>) * x "
proof -
  have rearrange: "(1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) = ((\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) + 1)" by auto
  show "ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))
      = 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f)  + wp (compile C) (\<lbrakk>b\<rbrakk>)  * x "
    unfolding rearrange    
    by (auto simp: wp1 decompose_wpert scale_unaffected_expectations_right)
qed

lemma assumes "fiid C b f"
    and [simp]: "unaffected (ert (compile C) 0) C"
        "deter C"
        "wp (compile C) 1 = 1" 
        "unaffected x C"  
shows deter_unaff_unroll:
      "unaffected (ert (compile C) (1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x)) C"
proof - 
  from assms have [simp]:"unaffected (wp (compile C) \<lbrakk>b\<rbrakk>) C"
        "unaffected (wp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C" unfolding fiid_def by auto
  
  have B: "ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) = ert (compile C) 0 + wp (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f)"
    by (auto simp: decompose_ert[symmetric])

  have [simp]: "unaffected 1 C"  unfolding unaffected_def Vars_def by auto

  show 2: "unaffected (ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))) C"
    by(auto simp: deter_decompose B intro!: unaffected_plus unaffected_mult)
qed


text \<open>This is the ert proof rule for f-iid loops. It is Theorem 4 in @{cite batzESOP18}.\<close>

theorem 
  fixes b :: "state \<Rightarrow> bool" and  f :: exp and C
  assumes wp1: "wp (compile C) 1 = 1" \<comment> \<open>loop body terminates almost-surely\<close>
    and "fiid C b f"
    and "unaffected (ert (compile C) 0) C" \<comment> \<open>every iteration runs in the same expected time\<close>
    and det: "deter C"
  shows prove_rule: "ert (compile (While b C)) f \<sigma> = 1 + (if b \<sigma> then (1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) \<sigma>)
                                                                          / (1- (wp (compile C) \<lbrakk>b\<rbrakk> \<sigma>))
                                                      else f \<sigma>)"
proof -    
  from assms have "unaffected (wp (compile C) \<lbrakk>b\<rbrakk>) C"
        "unaffected (wp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C" unfolding fiid_def by auto

  let ?f = "\<lambda>W. 1 + (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) + (\<lbrakk>b\<rbrakk>*W)"
  let ?g = "\<lambda>W. ert (compile C) W"
  let ?h = "\<lambda>s' r. 1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) s' + wp (compile C) \<lbrakk>b\<rbrakk> s' * r"
    
  have eq: "lfp (\<lambda>x. ?f (?g x)) = ?f (lfp (\<lambda>x. ?g (?f x)))"
    apply(rule lfp_rolling[where g="?f", symmetric])
     apply(auto simp: mono_def le_fun_def lift2_def) 
    using mono_ert[unfolded mono_def]
    by (smt le_fun_def)   

  have eq2: "(\<lambda>W x. 1 + (if b x then ert (compile C) W x else f x))
        =  (\<lambda>W. ?f (?g W))" unfolding lift2_def apply(rule) by auto
  have "ert (compile (While b C)) f = lfp (\<lambda>x. ?f (?g x))"
    by(simp add: eq2)   

  {
    fix s' :: state
  
    have *: "sup_continuous (\<lambda>x. ?g (?f x))" "sup_continuous (?h s)" for s :: state
      by (rule sup_continuous_compose[where f="ert (compile C)"]) (auto intro!: order_continuous_intros sup_continuous_ert) 

    from * have L: "lfp (\<lambda>W s. ?g (?f W) s) s' = lfp (%r. ?h s' r) \<and> unaffected (lfp (\<lambda>W s. ?g (?f W) s)) C"
    proof(induction rule: lfp_parallel_induct)
      case bot
      then show ?case by (auto simp: unaffected_def Vars_def) 
    next
      case (step x y)
      then have "unaffected x C" by auto
  
      have i: "ert (compile C) (1  + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))
            = 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + wp (compile C) (\<lbrakk>b\<rbrakk>) * x "
        apply (rule deter_decompose) by fact+ 

      have ii: "unaffected (ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))) C"
        apply(rule deter_unaff_unroll) by fact+

      show "?g (?f x) s' = ?h s' y \<and> unaffected (?g (?f x)) C"
        apply(safe)
        subgoal using i step by simp
        subgoal using ii by auto
        done
    next
      case (cont X Y)
      then show ?case apply (auto simp: unaffected_def Vars_def SUP_image)
        by (metis cont.IH unaffaccted_fun_upd) 
    qed 
  }
  then have "lfp (\<lambda>W s. ?g (?f W) s) \<sigma> = lfp (%r. ?h \<sigma> r)" by simp
  also have "\<dots> = (1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) \<sigma>) / (1 - wp (compile C) \<lbrakk>b\<rbrakk> \<sigma>)" (is "?A = ?B")
  proof (cases "wp (compile C) \<lbrakk>b\<rbrakk> \<sigma> < 1")
    case False
    with wp_le1 have is1: "wp (compile C) \<lbrakk>b\<rbrakk> \<sigma> = 1"
        by (metis lift2_def linear not_one_le_zero order.not_eq_order_implies_strict)
    then show "?A = ?B" by(subst lfp_linear_inf) (auto simp: add_pos_nonneg )
  qed (simp add: lfp_linear)

  finally have l: "lfp (\<lambda>W s. ?g (?f W) s) \<sigma> = (1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) \<sigma>) 
                      / (1 - wp (compile C) \<lbrakk>b\<rbrakk> \<sigma>)" 
    by auto


  show "ert (compile (While b C)) f \<sigma> =  1 + (if b \<sigma> then (1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) \<sigma>)
                                                               /  (1- (wp (compile C) \<lbrakk>b\<rbrakk> \<sigma>))
                                                      else f \<sigma>)"
    apply(simp) unfolding eq eq2   apply auto
     apply(subst l) unfolding lift2_def  by auto 
qed




section "New Prove Rule for non-deterministic"


lemma 
  decompose_wpert_awp: \<comment> \<open>generalization of @{thm decompose_wpert} to angelic weakest preexpectation.\<close>
  " ert (compile C) (f+g) \<le>  ert (compile C) f + awp (compile C) g"
proof (induct C arbitrary: f g) 
  case Skip
  then show ?case by (auto simp: nn_integral_add ac_simps)   
next
  case (Assign x1 x2)
  then show ?case by (auto simp: nn_integral_add ac_simps)   
next
  case (Seq C1 C2)
  have "ert (compile (C1;; C2)) (f+g) = ert (compile C1) (ert (compile C2) (f+g))" by auto
  also have "\<dots> \<le> ert (compile C1) (ert (compile C2) f + awp (compile C2) g)" by(intro monoD[OF mono_ert] Seq(2))
  also have "\<dots> \<le> ert (compile C1) (ert (compile C2) f) + awp (compile C1) (awp (compile C2) g)"
    by (intro monoD[OF mono_ert] Seq(1)) 
  also have "\<dots> = ert (compile (C1;; C2)) f + awp (compile (C1;; C2)) g" by auto  
  finally show ?case .
next  
  case (Par C1 C2) 
  thm sup.mono
  have "ert (compile C1) (f + g) \<squnion> ert (compile C2) (f + g) \<le> (ert (compile C1) f + awp (compile C1) g) \<squnion> (ert (compile C2) f + awp (compile C2) g)"
    by (intro sup.mono Par)
  also have "\<dots> \<le> (ert (compile C1) f \<squnion> ert (compile C2) f) + (awp (compile C1) g \<squnion> awp (compile C2) g)"
    by (intro sup_least add_mono) auto
  finally show ?case
    by (simp del: plus_fun_apply sup_apply) 
next
  case (If x1 C1 C2) then show ?case
    by (auto simp: le_fun_def ac_simps intro!: add_increasing[of 1 _ _]) 
next
  case (While b C)

  let ?P = "\<lambda>F W x. 1 + (if b x then ert (compile C) W x else F x)"
  let ?P' = "\<lambda>F W x. (if b x then awp (compile C) W x else F x)"
  have *: "\<And>F. mono (?P F)"
    by (auto simp: mono_def le_fun_def intro!: add_mono mono_ert[THEN monoD, THEN le_funD])
  have **: "\<And>F. mono (?P' F)"
    by (auto simp: mono_def le_fun_def intro!: add_mono mono_awp[THEN monoD, THEN le_funD])

  have "?P (\<lambda>x. f x + g x) (lfp (?P f) + lfp (?P' g)) \<le> ?P f (lfp (?P f)) + ?P' g (lfp (?P' g))"
    using While
    by (simp add: le_fun_def plus_fun_def) 
  also have "\<dots> = lfp (?P f) + lfp (?P' g)"
    unfolding lfp_unfold[OF *, symmetric] lfp_unfold[OF **, symmetric] ..
  finally show ?case
    by (clarsimp intro!: lfp_lowerbound simp add: plus_fun_def cong: if_cong)
 
qed 

corollary decompose_ert_awp: "ert (compile C) (f+g) s \<le>  ert (compile C) f s + awp (compile C) g s"
  using decompose_wpert_awp by (simp add: le_fun_def) 


corollary decompose_ert_awp0: "ert (compile C) f \<le> ert (compile C) 0 + awp (compile C) f"
  using decompose_wpert_awp[where f=0 and g=f] by auto 


lemma "Vars (ert (compile C) f) \<subseteq> Vars (ert (compile C) 0) \<union> Vars f"
  oops

(* counter example for monotonicity of awp *)

lemma "Vars f \<subseteq> Vars g \<Longrightarrow> Vars (awp (compile C) f) \<subseteq> Vars (awp (compile C) g)"
  oops

notepad begin
   define f :: exp where "f = (%s.   (1 - s ''y''))"
  define g :: exp where "g = (%s.   s ''y'')"
  define C :: spgcl where "C = Par (Assign ''y'' (\<lambda>s. return_pmf (1- s ''b''))) (Assign ''y'' (\<lambda>s. return_pmf (1)))"

  have f: "Vars f = {''y''}" apply (auto simp: Vars_def f_def)
    apply(rule exI[where x=1])
    apply(rule exI[where x=0])  by (auto )
        
  have g: "Vars g = {''y''}" by (auto simp: Vars_def g_def) 

                
  have af: "Vars (awp (compile C) f) = {''b''}" apply(auto simp: C_def Vars_def f_def)
    apply(rule exI[where x="1"])
    apply(rule exI[where x=0])   apply (auto simp: zero_ereal_def[symmetric] one_ereal_def[symmetric] one_ennreal_def[symmetric])
    by (metis le_sup_iff not_one_le_zero order_refl)

  have k: "\<And>v. of_nat (Suc 0 - v) \<le> (1::ennreal)"
    by (simp add: ennreal_of_nat_eq_real_of_nat) 
 
  have ag: "Vars (awp (compile C) g) = {}" apply(auto simp: C_def Vars_def g_def) 
    subgoal for v v' using k[of v] k[of v']
      by (simp add: sup.absorb2) 
    done

  from f g af ag have "~(Vars f \<subseteq> Vars g \<longrightarrow> Vars (awp (compile C) f) \<subseteq> Vars (awp (compile C) g))"
    by auto

  have i: "Vars (awp (compile C) 0) = {}" "Vars 0 = {}" by(auto simp: C_def Vars_def)

  {
    assume "\<And> F f g. Vars F \<subseteq> Vars f \<union> Vars g \<Longrightarrow> Vars (awp (compile C) F) \<subseteq> Vars (awp (compile C) f) \<union> Vars (awp (compile C) g)"

    from this[where F=f and f=0 and g=g] 
    have "Vars f \<subseteq> Vars g \<longrightarrow> Vars (awp (compile C) f) \<subseteq> Vars (awp (compile C) g)"
      unfolding i by auto
  }
end

(* counter example for unaff plus *)

lemma unaff_awp: "unaffected (awp (compile C) f) C \<Longrightarrow> unaffected (awp (compile C) g) C \<Longrightarrow> unaffected (awp (compile C) (f+g)) C"
  oops

text \<open>This rule - while being intuitive - is unfortunately wrong! here is a counterexample:\<close>

notepad
begin
 
  define f :: exp where "f = (%s. (if s ''x'' = 3 then 0 else (if s ''x''=1 then 1000 else (1 - s ''y''))))"
  define g :: exp where "g = (%s. (if s ''x'' = 3 then 0 else (if s ''x''=1 then (1 - s ''y'') else 1000)))"

  have fg: "f+g = (%s. (if s ''x'' = 3 then 0 else 1000 + (1 - s ''y'')))"
    unfolding f_def g_def by auto


  define C :: spgcl where "C = Par (Assign ''x'' (\<lambda>s. return_pmf 3);; Assign ''y'' (\<lambda>s. return_pmf 3))
                                (Par (Assign ''x'' (\<lambda>s. return_pmf 1)) (Assign ''x'' (\<lambda>s. return_pmf 2)))"

   
  then have k2: "\<And>v. (1 - of_nat v)\<le> (1000::ennreal)"
    by (metis ennreal_diff_le_mono_left of_nat_1 of_nat_mono of_nat_numeral one_le_numeral)

  have m: "Mod C = {''x'', ''y''}" by(auto simp: C_def)

  have i: "Vars (awp (compile C) f) = {}"
    apply(auto simp: Vars_def C_def f_def) 
    subgoal for v v' using k2[of v] k2[of v'] 
      by (simp add: sup.absorb2  sup.absorb1) 
    done

  have ii: "Vars (awp (compile C) g) = {}"
    apply(auto simp: Vars_def C_def g_def) 
    subgoal for v v' using k2[of v] k2[of v'] 
      by (simp add: sup.absorb2  sup.absorb1) 
    done

  have iii: "Vars (awp (compile C) (f+g)) = {''y''}"
    apply(auto simp: Vars_def C_def fg) 
    apply(rule exI[where x=0])
    apply(rule exI[where x=1]) 
    by (simp add: sup.absorb2)  


   have "\<not>(unaffected (awp (compile C) f) C \<longrightarrow> unaffected (awp (compile C) g) C \<longrightarrow> unaffected (awp (compile C) (f+g)) C)"
     unfolding unaffected_def i ii iii m by auto
end



theorem 
  fixes b :: "state \<Rightarrow> bool" and  f :: exp and C
  assumes (* "fiid C b f" and   ua: "unaffected (ert (compile C) 0) C" and *)
    awp1: "awp (compile C) 1 = 1" (* loop body terminates almost-surely *)
   and t: "\<And>x. unaffected x C \<Longrightarrow> unaffected (ert (compile C) (1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x)) C"
  shows prove_rule_awp: "ert (compile (While b C)) f s' \<le> 1 + (if b s' then (1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) s')
                                                                          / (1- (awp (compile C) \<lbrakk>b\<rbrakk> s'))
                                                      else f s')"
proof -    

  let ?f = "\<lambda>W. 1 + (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) + (\<lbrakk>b\<rbrakk>*W)"
  let ?g = "\<lambda>W. ert (compile C) W"
  let ?h = "%s' r. 1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) s' + awp (compile C) \<lbrakk>b\<rbrakk> s' * r"
    
  have eq: "lfp (\<lambda>x. ?f (?g x)) = ?f (lfp (\<lambda>x. ?g (?f x)))"
    apply(rule lfp_rolling[where g="?f", symmetric])
     apply(auto simp: mono_def le_fun_def lift2_def) 
    using mono_ert[unfolded mono_def]
    by (smt le_fun_def)   

  have eq2: "(\<lambda>W x. 1 + (if b x then ert (compile C) W x else f x))
        =  (\<lambda>W. ?f (?g W))" unfolding lift2_def apply(rule) by auto
  have "ert (compile (While b C)) f = lfp (\<lambda>x. ?f (?g x))"
    by(simp add: eq2)   

  {
    fix s' :: state
    assume x: "b s'" 
  
    have *: "sup_continuous (\<lambda>x. ?g (?f x))" "sup_continuous (?h s)" for s :: state
      by (rule sup_continuous_compose[where f="ert (compile C)"]) (auto intro!: order_continuous_intros sup_continuous_ert) 

    from * x have L: "lfp (\<lambda>W s. ?g (?f W) s) s' \<le> lfp (%r. ?h s' r) \<and> unaffected (lfp (\<lambda>W s. ?g (?f W) s)) C"
    proof(induction rule: lfp_parallel_induct)
      case bot
      then show ?case by (auto simp: unaffected_def Vars_def) 
    next
      case (step x y) 
      then have un_x[simp]: " unaffected x C" by simp

      { fix s' 
        have "ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))
              \<le> awp (compile C) 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + awp (compile C) (\<lbrakk>b\<rbrakk> * x)"
          (is "?A \<le> ?B")
        proof -                            
          have reorder: "(1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) = ((\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) + 1)" by auto
          have "?A = ert (compile C) ((\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) + 1)" by (simp add: reorder)
          also have "\<dots> \<le> ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x) + awp (compile C) 1"
            by (auto simp: decompose_wpert_awp) 
          also have "\<dots> \<le> ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f)  + awp (compile C) (\<lbrakk>b\<rbrakk> * x) + awp (compile C) 1"
            using decompose_wpert_awp add_right_mono by blast 
          finally show "?A \<le> ?B" by (simp add: ac_simps)
        qed 
      } note decompose=this
      
      have A: "ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x)) 
          \<le> awp (compile C) 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + awp (compile C) (\<lbrakk>b\<rbrakk> * x)"
        apply(rule decompose) done
      also have "\<dots> = 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + awp (compile C) (\<lbrakk>b\<rbrakk>) * x"
        by (auto simp: awp1 scale_unaffected_awp_right) 
      finally have A: "ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x)) 
          \<le> 1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f)  + awp (compile C) (\<lbrakk>b\<rbrakk>)  * x " by simp

      have B: "ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) \<le> ert (compile C) 0 + awp (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f)"
        by (rule decompose_ert_awp0) 

      have "unaffected 1 C"  unfolding unaffected_def Vars_def by auto

      {
        from un_x
        have 2: "unaffected (ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))) C"
          by(rule t)  
        (*
        from assms have "unaffected (wp (compile C) \<lbrakk>b\<rbrakk>) C"
            "unaffected (wp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C" unfolding fiid_def by auto
        then have a1: "unaffected (awp (compile C) \<lbrakk>b\<rbrakk>) C"
           and a2: "unaffected (awp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C" sorry


        from step have "unaffected x C" by simp
        then have a1': "unaffected (awp (compile C) (\<lbrakk>b\<rbrakk> * x)) C"
          apply(subst scale_unaffected_awp_right) apply simp
          apply(intro unaffected_mult) apply(rule a1) .

        have a3: "unaffected (awp (compile C) 1) C"
          unfolding awp1 unaffected_def Vars_def by auto

        have l: "(0 + (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x))) = (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x))" by auto
        from unaff_ert[OF ua unaff_awp[OF a3 unaff_awp[OF a2 a1']]]
        have 2: "unaffected (ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))) C"
          by (simp add: ab_semigroup_add_class.add_ac(1))
        *)
      } note 2 = this

      show ?case apply(safe) subgoal using A[THEN le_funD, of s', simplified] step
          by (meson ennreal_add_left_cancel_le mult_left_mono order_trans zero_le)
          subgoal using 2 by auto
        done
    next
      case (cont X Y)
      then show ?case apply (auto simp: unaffected_def Vars_def SUP_image)
        apply (simp add: SUP_subset_mono)        
        by (metis cont.IH unaffaccted_fun_upd) 
    qed 
  }
  then have "b s' \<Longrightarrow> lfp (\<lambda>W s. ?g (?f W) s) s' \<le> lfp (%r. ?h s' r)" by simp
  also have "\<dots> = (1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) s') / (1 - awp (compile C) \<lbrakk>b\<rbrakk> s')"  (is "?A = ?B")
  proof (cases "awp (compile C) \<lbrakk>b\<rbrakk> s' < 1")
    case False
    with awp_le1 have is1: "awp (compile C) \<lbrakk>b\<rbrakk> s' = 1"
        by (metis lift2_def linear not_one_le_zero order.not_eq_order_implies_strict)
    then show "?A = ?B" by(subst lfp_linear_inf) (auto simp: add_pos_nonneg )
  qed (simp add: lfp_linear)
  finally have l: "b s' \<Longrightarrow> lfp (\<lambda>W s. ?g (?f W) s) s' \<le> (1 + ert (compile C) (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) s') 
                      / (1 - awp (compile C) \<lbrakk>b\<rbrakk> s')"
    by auto


  show "ert (compile (While b C)) f s' \<le>  1 + (if b s' then (1 + ert (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f) s')
                                                               /  (1- (awp (compile C) \<lbrakk>b\<rbrakk> s'))
                                                      else f s')"
    apply(simp) unfolding eq eq2   apply auto
     using l unfolding lift2_def  by auto 
qed

(* with the preconditions of the deterministic case, 
 one can always show the compound assumption ("t" in prove_rule_awp),
 thus, prove_rule also is a corollary of prove_rule_awp *)
lemma assumes "fiid C b f"
    and "unaffected (ert (compile C) 0) C"
    and det: "deter C"
    and "awp (compile C) 1 = 1" 
    and "unaffected x C"  
shows
      "unaffected (ert (compile C) (1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x)) C"
proof -
  from assms awp_is_wp_if_deter have wp1: "wp (compile C) 1 = 1" by simp

  show ii: "unaffected (ert (compile C) (1 + (\<lbrakk>\<^bold>\<not> b\<rbrakk> * f) + (\<lbrakk>b\<rbrakk> * x))) C"
    apply(rule deter_unaff_unroll) by fact+  
qed

subsection "Example"

experiment 
begin

definition "innerb (N::nat) = (WHILE (%s. s ''b'' \<noteq> 1) DO
        Par (Assign ''b'' (%s. return_pmf 1)) (
        Assign ''b'' (%s. map_pmf (\<lambda>b. if b then 0 else 1)
                         (bernoulli_pmf (real (s ''a'') / N)))))"


definition "coco N = Assign ''b'' (\<lambda>s. return_pmf (0)) ;; Assign ''a'' (\<lambda>s. return_pmf (1)) ;; innerb N"




lemma fixes N::nat
  assumes N: "N>1"
  shows "ert (compile (coco N)) f s \<le> 3 + ( (1 + (1 + f (s(''a'' := Suc 0,''b'' := 1)))) * N) / (N -1)"
proof -
    
  { 
    fix f :: exp
    fix l::nat
    fix s :: state assume a: "s ''b'' = 0"  "s ''b'' = 0 \<or> s ''b''=1" "l<N" and b[simp]: "s ''a''=l"

    let ?S ="Par (Assign ''b'' (%s. return_pmf 1)) (
        Assign ''b'' (%s. map_pmf (\<lambda>b. if b then 0 else 1)
                         (bernoulli_pmf (real (s ''a'') / N))))"

    (* do not even need assumption unaffected x ?S *)
    have "\<And>f x b.  unaffected (ert (compile ?S) (1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x)) ?S"
      by (auto simp: Vars_def lift2_def unaffected_def) 
(*
    let ?S ="Par (Assign ''b'' (%s. return_pmf 1)) (
        Assign ''b'' (%s. map_pmf (\<lambda>b. if b then s ''c'' else 1)
                         (bernoulli_pmf (real (s ''a'') / N))))" 
    (* do not even need assumption unaffected x ?S *)
    have "\<And>f x b.  unaffected (ert (compile ?S) (1 + \<lbrakk>\<^bold>\<not> b\<rbrakk> * f + \<lbrakk>b\<rbrakk> * x)) ?S"
      apply (auto simp:   lift2_def unaffected_def) 
      apply(drule Vars_supD) apply safe
       apply(drule Vars_plusD) apply safe apply(simp add: Vars_def)
      subgoal by (auto simp: Vars_def lift2_def unaffected_def) 
      apply(drule Vars_plusD) apply safe  apply(simp add: Vars_def)  
    proof (goal_cases)
      case (1 f x b)
      thm Vars_integralD
      then show ?case  sorry
    qed
      apply(drule Vars_integralD) apply safe  apply(simp add: Vars_def)
      sorry
*)
    { 
      fix A :: ennreal assume "l<N"
      from N have "(1 - 1 / N)<1" by auto
      then have "A \<ge> (A * (1 - l / real N))" using \<open>l<N\<close>
        by (smt divide_nonneg_nonneg ennreal_le_1 mult.right_neutral mult_left_mono of_nat_0_le_iff zero_le)
      then have p: "A \<squnion> (A * (1 - real l / real N)) = A"
        using sup.absorb1 by blast 
    } note 1=this

    have "\<And>A B::ennreal. (1 + A) \<squnion> (1 + B) = 1 + (A \<squnion> B)"
      by (simp add: sup_const_add_ennreal) 

    have "(1 + (f (s(''b'' := Suc 0))) \<squnion> (1 + (f (s(''b'' := Suc 0))) * ennreal (1 - 1 / real N)))
          = (1 + (f (s(''b'' := Suc 0)))) \<squnion> ((1 + (f (s(''b'' := Suc 0))) * ennreal (1 - 1 / real N)))" by auto

    let ?S ="Par (Assign ''b'' (%s. return_pmf 1)) (
        Assign ''b'' (%s. map_pmf (\<lambda>b. if b then 0 else 1)
                         (bernoulli_pmf (real (s ''a'') / N))))"
    let ?b = "(%s. s ''b'' \<noteq> 1)" 
    have "ert (compile (innerb N)) f s \<le> 1 + (if ?b s then (1 + ert (compile ?S) (\<lbrakk>\<^bold>\<not>?b\<rbrakk>*f) s)
                                                                          / (1- (awp (compile ?S) \<lbrakk>?b\<rbrakk> s))
                                                      else f s)"
      unfolding innerb_def 
      apply(rule prove_rule_awp)
      subgoal by (auto 4 3)
      subgoal (* the hardest goal ? *)
         (* apply (auto dest!:  simp: unaffected_def lift2_def)
        apply(drule Vars_supD)                                                   
        apply safe subgoal apply(drule Vars_plusD) apply safe apply(simp add: Vars_def)
          by (auto simp: Vars_def)
        apply(drule Vars_plusD)
        apply safe 
         apply(simp add: Vars_def)
          *)
        by (auto simp: Vars_def lift2_def unaffected_def) (* I'm impressed by auto here *)
     done
   also have "\<dots> = 1 + (1 + (1 + (f (s(''b'' := Suc 0))) \<squnion> (1 + (f (s(''b'' := Suc 0))) * ennreal (1 - l / real N)))) / (1 - ennreal (l / real N))" 
     using a N by (auto simp: lift2_def sup.absorb2)
   also have "\<dots> = 1 + (1 + (1 + f (s(''b'' := Suc 0)))) / (1 - ennreal (l / real N))"
     apply (simp only: sup_const_add_ennreal ) using a by(simp only: 1)
    finally   
    have "ert (compile (innerb N)) f s \<le> 1 + (1 + (1 + f (s(''b'' := 1)))) / (1 - ennreal (l / real N))" by simp 
  } note k=this
 
  from N have *: "\<And>l. 1 - real l / real N = (real N - l) / real N"
    by(simp add: diff_divide_distrib) 
  have l: "(2::ennreal) = ennreal 2" by auto
  { fix A :: ennreal and l assume l: "l<N"
    have i: "1 / (1 - ennreal (real l / real N)) = N / (N-l)"  
      using N using l apply(auto simp del: ennreal_1 simp add: ennreal_minus ennreal_1[symmetric] divide_ennreal)
      unfolding * by auto 
    have "A / (1 - ennreal (real l / real N)) = A * (1 / (1 - ennreal (real l / real N)))"
      by (simp add: divide_ennreal_def)  
    also have "\<dots> = A * (N / (N-l))" unfolding i by auto
    also have "\<dots>=  (A * N) / (N - l)"  
      by (metis l divide_ennreal ennreal_of_nat_eq_real_of_nat ennreal_times_divide of_nat_0_le_iff of_nat_0_less_iff zero_less_diff)   
    finally have eq: "A / (1 - ennreal (l / real N))                                              
        =  (A * N) / (N - l)" .
  } note pf=this

  { fix l assume l: "l<N"
        have "ert (compile (innerb N)) f (s(''b'' := 0, ''a'' := l))
        \<le> 1 + (1 + (1 + f ((s(''b'' := 0, ''a'' := l))(''b'' := 1)))) / (1 - ennreal (l / N))" apply(rule k)
          using l by auto
      also have "\<dots> = 1 + (1 + (1 + f (s(''a'' := l, ''b'' := 1)))) * of_nat N / of_nat (N - l)" apply(subst pf)
       using l by auto
      finally have 
      "ert (compile (innerb N)) f (s(''b'' := 0, ''a'' := l)) \<le> 1 + ( (1 + (1 + f (s(''a'' := l,''b'' := 1)))) * N) / (N -l)"
        .
    } note i=this

  show ?thesis unfolding coco_def apply auto
    using i[of 1] N apply auto
    by (metis (no_types, lifting) One_nat_def Suc_numeral add_numeral_left ennreal_add_left_cancel_le numeral_3_eq_3 numeral_One numeral_eq_iff)  
qed

end



end