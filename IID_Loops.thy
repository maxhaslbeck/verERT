\<^marker>\<open>creator "Maximilian P.L. Haslbeck"\<close>
chapter "Expected runtimes of i.i.d. loops"
theory IID_Loops
imports PGCL_With_State
begin


paragraph \<open>Summary\<close>

text \<open>This theory follows the beginning of Section 4 of @{cite batzESOP18},
      it formalizes when a expecation is @{term unaffected} by a program,
      and what iid-loops are.\<close>


paragraph \<open>Main definitions\<close>

text \<open>
  \<^item> Mod: the variables a program modifies
  \<^item> Var: the variables of a expectation
  \<^item> unaffected: predicate that characterizes when an expectation is unaffected by a program
  \<^item> fiid: f-Independent and Identically Distributed Loops
 \<close>

paragraph \<open>Main theorems\<close>

text \<open>
  \<^item> scale_unaffected_expectations: Lemma 1 (Scaling of Unaffected Expectations) of @{cite batzESOP18}
  \<^item> scale_unaffected_awp: a generalization to angelic weakest preexpectation
\<close>
 


subsection "Mod: set of modified variables"

fun Mod :: "spgcl \<Rightarrow> vname set" where
 "Mod Skip = {}"
(* |  "Mod Empty = {}"
| "Mod Halt = {}" *)
| "Mod (Assign v _) = {v}"
| "Mod (Seq c1 c2) = Mod c1 \<union> Mod c2"
| "Mod (Par c1 c2) = Mod c1 \<union> Mod c2"
| "Mod (If b c1 c2) = Mod c1 \<union> Mod c2"
| "Mod (While b c) = Mod c"

 
subsection "unaffected"

definition Vars :: "exp \<Rightarrow> vname set" where 
  "Vars f = {x | x. \<exists>s v v'. f(s(x:=v)) \<noteq> f(s(x:=v'))}"


lemma Vars_plus: "Vars (f+g) \<subseteq> Vars f \<union> Vars g"
  unfolding Vars_def apply auto by metis

lemma Vars_plusD: "x \<in> Vars (f+g) \<Longrightarrow> x : Vars f \<or> x : Vars g "
  using Vars_plus by blast


(*
lemma Vars_integral: "Vars (\<lambda>xa. \<integral>\<^sup>+ y. f xa y \<partial>measure_pmf (P xa)) \<subseteq> UNION UNIV (\<lambda>s. UNION (set_pmf P s) (\<lambda>t. Vars (\<lambda>s. f s t)))"
  unfolding Vars_def apply auto sorry

lemma Vars_integralD: "x \<in> Vars (\<lambda>xa. \<integral>\<^sup>+ y. f xa y \<partial>measure_pmf (P xa)) \<Longrightarrow> (\<exists>xa . \<exists> t \<in>set_pmf P xa . x \<in> Vars (\<lambda>s. f s t))"
  using Vars_integral  by blast
*)


lemma Vars_mult: "Vars (f*g) \<subseteq> Vars f \<union> Vars g"
  unfolding Vars_def apply auto by metis

lemma Vars_sup: "Vars (f\<squnion>g) \<subseteq> Vars f \<union> Vars g"
  unfolding Vars_def apply auto by metis 

lemma Vars_supD: "x \<in> Vars (f\<squnion>g) \<Longrightarrow> x : Vars f \<or> x : Vars g "
  using Vars_sup by blast


lemma Vars_sup': "Vars (\<lambda>s. f s \<squnion> g s) \<subseteq> Vars f \<union> Vars g"
  unfolding Vars_def apply auto by metis
 


lemma Vars_const: "Vars (%_. c) = {}" unfolding Vars_def by auto
 

definition unaffected :: "exp \<Rightarrow> spgcl \<Rightarrow> bool" where
 "unaffected f C \<longleftrightarrow> Vars f \<inter> Mod C = {}" 

lemma unaffected_bot: "unaffected \<bottom> C" 
  unfolding unaffected_def Vars_def by auto

lemma unaffected_const: "unaffected (%_. c) C" 
  unfolding unaffected_def Vars_const by auto
 

lemma unaffected_plus: "unaffected f C \<Longrightarrow> unaffected g C \<Longrightarrow> unaffected (f+g) C"
  unfolding unaffected_def using Vars_plus by blast 

lemma unaffected_mult: "unaffected f C \<Longrightarrow> unaffected g C \<Longrightarrow> unaffected (f*g) C"
  unfolding unaffected_def using Vars_mult by blast 

lemma unaffected_Seq: assumes "unaffected g (C1;; C2)"
  shows "unaffected g C1" and "unaffected g C2"
  using assms by(auto simp: unaffected_def)


lemma unaffected_Par: assumes "unaffected g (Par C1 C2)"
  shows "unaffected g C1" and "unaffected g C2"
  using assms by (auto simp: unaffected_def)

lemma unaffected_If: assumes "unaffected g (If b C1 C2)"
  shows "unaffected g C1" and "unaffected g C2"
  using assms by(auto simp: unaffected_def)

lemma assumes "unaffected f C" "x1 \<in> Mod C"
  shows  unaffaccted_fun_upd: "f (s(x1:=v)) = f s"
proof -
  from assms have "x1 \<notin> Vars f" by (auto simp: unaffected_def)
  then have "\<And>s v v'. f (s(x1 := v)) = f (s(x1 := v'))" by (auto simp: Vars_def)
  from this[of s v "s x1"] show ?thesis by auto
qed

subsubsection "unaffected wp"


lemma \<comment> \<open> Lemma 1 (Scaling of Unaffected Expectations) of @{cite batzESOP18}  \<close>
  fixes f g :: exp
  shows scale_unaffected_expectations: "unaffected g C \<Longrightarrow> wp (compile C) (g * f) = g * (wp (compile C) f)"
proof (induct C arbitrary: f)
  case (Assign x1 x2) 
  thus ?case by (auto simp: unaffaccted_fun_upd nn_integral_cmult)   
next
  case (Seq C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Seq)
  have "wp (compile (C1;; C2)) (g * f) =
        wp (compile C1) (wp (compile C2) (g * f))" by simp
  also have "wp (compile C1) (wp (compile C2) (g * f)) = g * (wp (compile C1) (wp (compile C2) f))"
    using u1 u2 by(simp only: Seq)
  also have "\<dots> = g * wp (compile (C1;; C2)) f" by auto
  finally show ?case .
next
  case (If b C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_If)
  have "wp (compile (If b C1 C2)) (g * f) =
        (\<lambda>x. if b x then wp (compile C1) (g * f) x else wp (compile C2) (g * f) x)" by simp
  also have "\<dots> = (\<lambda>x. if b x then (g * (wp (compile C1) f)) x else (g * (wp (compile C2) f)) x)"
    using u1 u2 by(simp only: If) 
  also have "\<dots> = g * wp (compile (If b C1 C2)) f" by auto
  finally show ?case .
next
  case (While b C)
  then have u: "unaffected g C" unfolding unaffected_def by auto 

  let ?f = "(\<lambda>W x. if b x then wp (compile C) W x else (g * f) x)"
  let ?g = "(\<lambda>W x. if b x then wp (compile C) W x else f x)"
  have "sup_continuous ?f" "sup_continuous ?g"
    by (auto intro!: order_continuous_intros sup_continuous_wp[THEN sup_continuous_applyD])
  thus "wp (compile (WHILE b DO C)) (g * f) =  g* wp (compile (WHILE b DO C)) f"
  proof(clarsimp, induct rule: lfp_parallel_induct)
    case (step x y)
    thus ?case using While(1)[OF u] by auto
  qed (auto simp: bot0 SUP_mult_left_ennreal SUP_image)
next
  case (Par C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Par)
  with Par(1,2) have 1: "\<And>f. wp (compile C1) (g * f) = g * wp (compile C1) f"
      and 2:  "\<And>f. wp (compile C2) (g * f) = g * wp (compile C2) f"
    by blast+    
  show ?case apply(simp only: wp.simps compile.simps)
    apply(subst 1) apply (subst 2) 
    apply(rule)  
    apply (auto  )
    by (smt inf_absorb1 inf_absorb2 linear mult_left_mono zero_le)   
qed auto


lemma
  fixes f g :: exp
  shows scale_unaffected_expectations_right: "unaffected g C \<Longrightarrow> wp (compile C) (f * g) = (wp (compile C) f) * g"
  using scale_unaffected_expectations by (metis mult.commute)

lemma assumes "unaffected g C" 
  shows scale_unaffected_expectations_iter: "wp (compile C) (A * (%s. g s ^ n)) = wp (compile C) A * (\<lambda>s. g s ^ n)"
proof (induct n)
  case (Suc n)
  have i: "(A * (\<lambda>s. (g s ^ n) * g s )) = ((A * (\<lambda>s. (g s ^ n))) * g)"
      by ( auto simp add: mult.commute mult.left_commute) 
  have "wp (compile C) (A * (\<lambda>s. g s ^ Suc n)) = wp (compile C) (A * (\<lambda>s. (g s ^ n) * g s ))"
    by (simp only: power_Suc2)
  also have "\<dots> = wp (compile C) ((A * (\<lambda>s. (g s ^ n))) * g)" by(simp only: i) 
  also have "\<dots> = wp (compile C) (A * (\<lambda>s. (g s ^ n))) * g" apply(rule scale_unaffected_expectations_right) by fact 
  also have "\<dots> = wp (compile C) A * (\<lambda>s. g s ^ n) * g" by(simp only: Suc)
  also have "\<dots> = wp (compile C) A * ((\<lambda>s. g s ^ n) * g)" by (simp add: mult.assoc) 
  also have "\<dots> = wp (compile C) A * (\<lambda>s. g s ^ n  * g s)"by (simp add: times_fun_def)
  also have "\<dots> = wp (compile C) A * (\<lambda>s. g s ^ Suc n)" by (simp only: power_Suc2)
  finally show ?case .
qed simp 


subsubsection "unaffected awp"

(* TODO: should that actually hold?
lemma
  fixes f g :: exp
  shows plus_unaffected_awp: "unaffected g C \<Longrightarrow> awp (compile C) (g + f) = g + (awp (compile C) f)"
proof (induct C arbitrary: f)
  case (Assign x1 x2) 
  thus ?case by (auto simp: unaffaccted_fun_upd nn_integral_cmult nn_integral_linear[where a=1, simplified]) 
next
  case (Seq C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Seq)
  have "awp (compile (C1;; C2)) (g + f) =
        awp (compile C1) (awp (compile C2) (g + f))" by simp
  also have "awp (compile C1) (awp (compile C2) (g + f)) = g + (awp (compile C1) (awp (compile C2) f))"
    using u1 u2 by(simp only: Seq)
  also have "\<dots> = g + awp (compile (C1;; C2)) f" by auto
  finally show ?case .
next
  case (If b C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_If)
  have "awp (compile (If b C1 C2)) (g + f) =
        (\<lambda>x. if b x then awp (compile C1) (g + f) x else awp (compile C2) (g + f) x)" by simp
  also have "\<dots> = (\<lambda>x. if b x then (g + (awp (compile C1) f)) x else (g + (awp (compile C2) f)) x)"
    using u1 u2 by(simp only: If) 
  also have "\<dots> = g + awp (compile (If b C1 C2)) f" by auto
  finally show ?case .
next
  case (While b C)
  then have u: "unaffected g C" unfolding unaffected_def by auto 


  let ?f = "(\<lambda>W x. if b x then awp (compile C) W x else (g + f) x)"
  let ?g = "(\<lambda>W x. if b x then awp (compile C) W x else f x)"
  have "sup_continuous ?f" "sup_continuous ?g"
    by (auto intro!: order_continuous_intros sup_continuous_awp[THEN sup_continuous_applyD])
  thus "awp (compile (WHILE b DO C)) (g + f) =  g+ awp (compile (WHILE b DO C)) f"
    apply (clarsimp) sorry (*
  proof( induct rule: lfp_parallel_induct)
    case bot
    then show ?case apply (auto simp: bot0 SUP_mult_left_ennreal) sorry
  next
    case (step x y)
    thus ?case using While(1)[OF u] by auto
  next
    case (cont X Y)
    then show ?case apply (auto simp: bot0 SUP_mult_left_ennreal) by (simp add: ennreal_SUP_add_right)
  qed *)
next
  case (Par C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Par)
  with Par(1,2) have 1: "\<And>f. awp (compile C1) (g + f) = g + awp (compile C1) f"
      and 2:  "\<And>f. awp (compile C2) (g + f) = g + awp (compile C2) f"
    by blast+    
  show ?case apply(simp only: awp.simps compile.simps)
    apply(subst 1) apply (subst 2)  
    by (auto simp add: sup_const_add_ennreal)  
qed auto *)

lemma \<comment> \<open> generalization of Lemma 1 (Scaling of Unaffected Expectations) of @{cite batzESOP18}
          for angelic weakest preexpectation  \<close>
  fixes f g :: exp
  shows scale_unaffected_awp: "unaffected g C \<Longrightarrow> awp (compile C) (g * f) = g * (awp (compile C) f)"
proof (induct C arbitrary: f)
  case (Assign x1 x2) 
  thus ?case by (auto simp: unaffaccted_fun_upd nn_integral_cmult)   
next
  case (Seq C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Seq)
  have "awp (compile (C1;; C2)) (g * f) =
        awp (compile C1) (awp (compile C2) (g * f))" by simp
  also have "awp (compile C1) (awp (compile C2) (g * f)) = g * (awp (compile C1) (awp (compile C2) f))"
    using u1 u2 by(simp only: Seq)
  also have "\<dots> = g * awp (compile (C1;; C2)) f" by auto
  finally show ?case .
next
  case (If b C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_If)
  have "awp (compile (If b C1 C2)) (g * f) =
        (\<lambda>x. if b x then awp (compile C1) (g * f) x else awp (compile C2) (g * f) x)" by simp
  also have "\<dots> = (\<lambda>x. if b x then (g * (awp (compile C1) f)) x else (g * (awp (compile C2) f)) x)"
    using u1 u2 by(simp only: If) 
  also have "\<dots> = g * awp (compile (If b C1 C2)) f" by auto
  finally show ?case .
next
  case (While b C)
  then have u: "unaffected g C" unfolding unaffected_def by auto 

  let ?f = "(\<lambda>W x. if b x then awp (compile C) W x else (g * f) x)"
  let ?g = "(\<lambda>W x. if b x then awp (compile C) W x else f x)"
  have "sup_continuous ?f" "sup_continuous ?g"
    by (auto intro!: order_continuous_intros sup_continuous_awp[THEN sup_continuous_applyD])
  thus "awp (compile (WHILE b DO C)) (g * f) =  g* awp (compile (WHILE b DO C)) f"
  proof(clarsimp, induct rule: lfp_parallel_induct)
    case (step x y)
    thus ?case using While(1)[OF u] by auto
  qed (auto simp: bot0 SUP_mult_left_ennreal SUP_image)
next
  case (Par C1 C2)
  then have u1: "unaffected g C1" and u2: "unaffected g C2" by(auto dest: unaffected_Par)
  with Par(1,2) have 1: "\<And>f. awp (compile C1) (g * f) = g * awp (compile C1) f"
      and 2:  "\<And>f. awp (compile C2) (g * f) = g * awp (compile C2) f"
    by blast+    
  show ?case apply(simp only: awp.simps compile.simps)
    apply(subst 1) apply (subst 2) 
    apply(rule)  
    apply (auto  )
    by (smt sup_absorb1 sup_absorb2 linear mult_left_mono zero_le)   
qed auto


lemma
  fixes f g :: exp
  shows scale_unaffected_awp_right: "unaffected g C \<Longrightarrow> awp (compile C) (f * g) = (awp (compile C) f) * g"
  using scale_unaffected_awp by (metis mult.commute)

lemma assumes "unaffected g C" 
  shows scale_unaffected_awp_iter: "awp (compile C) (A * (%s. g s ^ n)) = awp (compile C) A * (\<lambda>s. g s ^ n)"
proof (induct n)
  case (Suc n)
  have i: "(A * (\<lambda>s. (g s ^ n) * g s )) = ((A * (\<lambda>s. (g s ^ n))) * g)"
      by ( auto simp add: mult.commute mult.left_commute) 
  have "awp (compile C) (A * (\<lambda>s. g s ^ Suc n)) = awp (compile C) (A * (\<lambda>s. (g s ^ n) * g s ))"
    by (simp only: power_Suc2)
  also have "\<dots> = awp (compile C) ((A * (\<lambda>s. (g s ^ n))) * g)" by(simp only: i) 
  also have "\<dots> = awp (compile C) (A * (\<lambda>s. (g s ^ n))) * g" apply(rule scale_unaffected_awp_right) by fact 
  also have "\<dots> = awp (compile C) A * (\<lambda>s. g s ^ n) * g" by(simp only: Suc)
  also have "\<dots> = awp (compile C) A * ((\<lambda>s. g s ^ n) * g)" by (simp add: mult.assoc) 
  also have "\<dots> = awp (compile C) A * (\<lambda>s. g s ^ n  * g s)"by (simp add: times_fun_def)
  also have "\<dots> = awp (compile C) A * (\<lambda>s. g s ^ Suc n)" by (simp only: power_Suc2)
  finally show ?case .
qed simp 


section "f-Independent and Identically Distributed Loops" 

definition "fiid C b f \<longleftrightarrow> unaffected (wp (compile C) \<lbrakk>b\<rbrakk>) C
                            \<and> unaffected (wp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C"
 
lemma assumes "fiid C b f" 
  shows fiid_D1:"unaffected (wp (compile C) \<lbrakk>b\<rbrakk>) C"
       and fiid_D2:  "unaffected (wp (compile C) (\<lbrakk>\<^bold>\<not>b\<rbrakk>*f)) C"
  using assms unfolding fiid_def by auto

end