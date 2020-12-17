\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
theory StateProg
imports MDP_Semantics PGCLMisc
begin




section "PGCL with explicit state"

type_synonym vname = string
type_synonym val = nat
type_synonym state = "vname \<Rightarrow> val"


datatype spgcl = (* Empty *)
                  Skip 
                (* | Halt *)
                 | Assign vname "state \<Rightarrow> val pmf"
                 | Seq (left: "spgcl") (right: "spgcl") ("_;;/ _"  [60, 61] 60)
                 | Par (left: "spgcl") (right: "spgcl") 
                 | If "state \<Rightarrow> bool" (left: "spgcl") (right: "spgcl")
                 | While "state \<Rightarrow> bool" "spgcl" ("(WHILE _/ DO _)"  [0, 61] 61)
 

fun compile :: "spgcl \<Rightarrow> state pgcl" where
 "compile Skip = PGCL.Skip"
(* |  "compile Empty = PGCL.Empty"
| "compile Halt = PGCL.Halt" *)
| "compile (Assign v f) = PGCL.Assign (\<lambda>s. map_pmf (\<lambda>r. s(v:=r)) (f s))"
| "compile (Seq c1 c2) = PGCL.Seq (compile c1) (compile c2)"
| "compile (Par c1 c2) = PGCL.Par (compile c1) (compile c2)" 
| "compile (If b c1 c2) = PGCL.If b (compile c1) (compile c2)" 
| "compile (While b c) = PGCL.While b (compile c)" 


fun deter :: "spgcl \<Rightarrow> bool" where
 "deter Skip = True"
(* |  "compile Empty = PGCL.Empty"
| "compile Halt = PGCL.Halt" *)
| "deter (Assign v f) = True"
| "deter (Seq c1 c2) = (deter c1 \<and> deter c2)"
| "deter (Par c1 c2) = False" 
| "deter (If b c1 c2) = (deter c1 \<and> deter c2)"
| "deter (While b c) = deter c"







type_synonym exp = "(state \<Rightarrow> ennreal)"

lemma bot0: "(\<bottom>::exp) = 0"  
  by (metis bot.not_eq_extremum gr_implies_not_zero)

subsection "syntax"

definition lift2 :: "(state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> ennreal" ("\<lbrakk>_\<rbrakk>") where
  "lift2 b = (\<lambda>s. if b s then 1 else 0)"

lemma lift2_fold: "(\<lambda>s. if b s then f s else 0) = lift2 b * f"
        unfolding lift2_def by auto

abbreviation NOT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" ("\<^bold>\<not>") where
  "NOT b \<equiv> (\<lambda>a. \<not> b a)"

subsection "wp and ert Orbits"


definition chara where
  "chara b C f W  = (\<lambda>s::state. if b s then wp (compile C) W s else f s)" 

lemma fixes i j
  shows chara_mono: "i\<le>j \<Longrightarrow> (chara b C f ^^ i) \<bottom> s \<le> (chara b C f ^^ j) \<bottom> s"
proof(induct arbitrary: s rule: diff_induct)
  case (1 x)
  then show ?case by auto
next
  case (2 y)
  show ?case
    apply(induct y) by auto 
next
  case (3 x y) 
  have *: "\<And>f g s. f \<le> g \<Longrightarrow>  wp (compile C) f s \<le> wp (compile C) g s"
    by (simp add: mono_wp[unfolded mono_def] le_funD) 

  from 3 show ?case apply auto unfolding chara_def apply auto
    apply(subst *) apply auto
    using le_funI by blast 
qed


lemma chara_alt: "chara b C f W = (lift2 b) * wp (compile C) W + (lift2 (\<lambda>s. ~ b s)) * f"
  unfolding chara_def lift2_def by auto

definition charaErt where
  "charaErt b C f W  = (\<lambda>s::state. 1 + (if b s then ert (compile C) W s else f s) )" 


lemma fixes i j
  shows charaErt_mono: "i\<le>j \<Longrightarrow> (charaErt b C f ^^ i) \<bottom> s \<le> (charaErt b C f ^^ j) \<bottom> s"
proof(induct arbitrary: s rule: diff_induct)
  case (1 x)
  then show ?case by auto
next
  case (2 y)
  show ?case
    apply(induct y) by auto 
next
  case (3 x y)
  have *: "\<And>f g s. f \<le> g \<Longrightarrow>  ert (compile C) f s \<le> ert (compile C) g s"
    by (simp add: mono_ert[unfolded mono_def] le_funD) 

  from 3 show ?case apply auto unfolding charaErt_def apply auto
    apply(subst *) apply auto
    using le_funI by blast 
qed

lemma charaErt_alt: "charaErt b C f W = 1 + (lift2 b) * ert (compile C) W + (lift2 (\<lambda>s. ~ b s)) * f"
  unfolding charaErt_def lift2_def by auto

lemma wp_sup: "wp (compile (While b C)) f  = (\<Squnion>i. ((chara b C f) ^^ i) \<bottom>)"
  unfolding chara_def apply simp
  apply(rule sup_continuous_lfp) 
  by (auto intro!: order_continuous_intros simp add:   sup_continuous_wp sup_continuous_applyD)

lemma ert_sup: "ert (compile (While b C)) f = (\<Squnion>i. ((charaErt b C f) ^^ i) \<bottom>)"
  unfolding charaErt_def apply simp
  apply(rule sup_continuous_lfp) 
  by (auto intro!: order_continuous_intros simp add:   sup_continuous_ert sup_continuous_applyD)

subsection "Decompose ert into wp and ert"

(* this stems from spgcl being deterministic *)

lemma 
  decompose_wpert: (* Olmedo,Kaminski,Katoen,Matheja - Reasoning about Recursive Probabilistic Programs *)
  "deter C \<Longrightarrow> ert (compile C) (f+g) =  ert (compile C) f + wp (compile C) g"
proof (induct C arbitrary: f g) 
  case (Seq C1 C2)
  then have "deter C1" "deter C2" by auto
  have "ert (compile (C1;; C2)) (f+g) = ert (compile C1) (ert (compile C2) (f+g))" by auto
  also have "\<dots> = ert (compile C1) (ert (compile C2) f + wp (compile C2) g)" apply(subst Seq(2)) apply fact by simp
  also have "\<dots> = ert (compile C1) (ert (compile C2) f) + wp (compile C1) (wp (compile C2) g)"
    apply (subst Seq(1)) apply fact by simp
  also have "\<dots> = ert (compile (C1;; C2)) f + wp (compile (C1;; C2)) g" by auto  
  finally show ?case .
next
  case (If x1 C1 C2)
  then have If': "\<And>f g. ert (compile C1) (f + g) = ert (compile C1) f + wp (compile C1) g" 
        "\<And>f g. ert (compile C2) (f + g) = ert (compile C2) f + wp (compile C2) g"  
    by fastforce+
  have t: "(\<lambda>a. f a + g a) = f+g" by auto
  show ?case by (auto simp: If' t )
next
  case (While b C)
  then have While': "\<And>f g. ert (compile C) (f + g) = ert (compile C) f + wp (compile C) g"
    by fastforce
  let ?C ="charaErt b C"
  let ?W ="chara b C"

  { fix i
    have i: "(?C (f+g) ^^ i) \<bottom> = (?C f ^^ i) \<bottom> + (?W g ^^ i) \<bottom>"
    proof(induct i) 
      case (Suc i)
      have "(?C (f+g) ^^ Suc i) \<bottom> = ?C (f+g) ((?C (f+g) ^^ i) \<bottom>)" by auto
      also have "\<dots> = ?C f ((?C f ^^ i) \<bottom>) + ?W g ((?W g ^^ i) \<bottom>)"
        apply(subst charaErt_def)
        apply(subst charaErt_def)
        apply(subst chara_def) apply(rule) apply auto
        apply(subst Suc) by(auto simp: While') 
      also have "\<dots> = (?C f ^^ Suc i) \<bottom> + (?W g ^^ Suc i) \<bottom>" by auto      
      finally show ?case .
    qed auto
  } note 1=this

  have "ert (compile (WHILE b DO C)) (f+g) = (\<Squnion>i. (?C (f+g) ^^ i) \<bottom>)" by(rule ert_sup) 
  also have "\<dots> = (\<Squnion>i. (?C f ^^ i) \<bottom> + (?W g ^^ i) \<bottom>)" by(simp only: 1)
  also have "\<dots> = (\<Squnion>i. (?C f ^^ i) \<bottom>) + (\<Squnion>i. (?W g ^^ i) \<bottom>)"
    apply(auto simp: SUP_image intro!: ext SUP_add_directed_ennreal)
    subgoal for s i j apply (rule exI[where x="max i j"])  by(auto simp add: chara_mono charaErt_mono add_mono)
    done
  also have "\<dots> = ert (compile (WHILE b DO C)) f + wp (compile (WHILE b DO C)) g"
    by(simp only: ert_sup wp_sup)

  finally show ?case .
qed (auto simp: nn_integral_add)

corollary decompose_ert: "deter C \<Longrightarrow> ert (compile C) f =  ert (compile C) 0 + wp (compile C) f"
  using decompose_wpert[where f=0 and g=f] by auto 


corollary decompose_ert': "deter C \<Longrightarrow> ert (compile C) (f+g) s =  ert (compile C) f s + wp (compile C) g s"
  using decompose_wpert[where f=f and g=g] by auto


subsection "Linearity of wp" 

lemma wp_linear: "deter C \<Longrightarrow> a < \<infinity> \<Longrightarrow> wp (compile C) ((\<lambda>s. a * f1 s) + f2) = (\<lambda>s. (a::ennreal) * wp (compile C) f1 s) + wp (compile C) f2"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?P C f1 f2 a")
proof (induct C arbitrary: f1 f2 a)
  case (Assign x1 x2)
  then show ?case   by (auto simp add: nn_integral_add  nn_integral_cmult)
next
  case (Seq C1 C2) 
  then have Seq': "\<And>f1 f2. wp (compile C1) ((\<lambda>s. a * f1 s) + f2) 
                = (\<lambda>s. a * wp (compile C1) f1 s) + wp (compile C1) f2" 
 "\<And>f1 f2. wp (compile C2) ((\<lambda>s. a * f1 s) + f2) 
                = (\<lambda>s. a * wp (compile C2) f1 s) + wp (compile C2) f2" 
    by fastforce+
      
  show ?case by (simp only: compile.simps wp.simps Seq')  
next
  case (While b C)
  then have While': "\<And>f1 f2. ?P C f1 f2 a" by force
  {
    fix i
    let ?C ="chara b C"
    have "(?C ((\<lambda>s. a * f1 s) + f2) ^^ i) \<bottom> = (%s. a * ((?C f1 ^^ i) \<bottom> s))  + (?C f2 ^^ i) \<bottom>"
    proof (induct i)
      case 0
      then show ?case by (auto simp: bot0) 
    next
      case (Suc i)
      have "(?C ((\<lambda>s. a * f1 s) + f2) ^^ Suc i) \<bottom> = ?C ((\<lambda>s. a * f1 s) + f2) ((?C ((\<lambda>s. a * f1 s) + f2) ^^ i) \<bottom>)" by auto
      also have "\<dots> = (\<lambda>s. a * ?C f1 ((?C f1 ^^ i) \<bottom>) s) + ?C f2 ((?C f2 ^^ i) \<bottom>)"
        apply(subst Suc)
        apply(subst chara_def) apply(subst chara_def) apply(subst chara_def) apply(rule) 
        apply(subst While')  
        using While(2) by auto
      also have "\<dots> = (\<lambda>s. a * (chara b C f1 ^^ Suc i) \<bottom> s) + (?C f2 ^^ Suc i) \<bottom>" by auto      
      finally show ?case .
    qed
  } note 1=this

  have *: "(\<lambda>s. a * (\<Squnion>i. (chara b C f1 ^^ i) \<bottom>) s) = (\<Squnion>i. (\<lambda>s. a * ((chara b C f1 ^^ i) \<bottom> s)) )" 
    by (auto simp: SUP_image SUP_mult_left_ennreal) 
  have "wp (compile (WHILE b DO C)) ((\<lambda>s. a * f1 s) + f2)
      = (\<Squnion>i. (chara b C ((\<lambda>s. a * f1 s) + f2) ^^ i) \<bottom>)" by(rule wp_sup)
  also have "\<dots> = (\<Squnion>i. (\<lambda>s. a * ((chara b C f1 ^^ i) \<bottom> s))  + (chara b C f2 ^^ i) \<bottom>)" 
    by(simp only: 1)
  also have "\<dots> = (\<Squnion>i. (\<lambda>s. a * ((chara b C f1 ^^ i) \<bottom> s)) ) + (\<Squnion>i. (chara b C f2 ^^ i) \<bottom>)"   
    proof -
    show ?thesis apply (auto simp: SUP_image intro!: ext SUP_add_directed_ennreal)      
      subgoal for s i j apply (rule exI[where x="max i j"]) 
        by (simp add: chara_mono mult_left_mono add_mono)   
      done
  qed
  also have "\<dots> = (\<lambda>s. a * (\<Squnion>i. (chara b C f1 ^^ i) \<bottom>) s) + (\<Squnion>i. (chara b C f2 ^^ i) \<bottom>)" 
    by(simp only: *)
  also have "\<dots> = (\<lambda>s. a * wp (compile (WHILE b DO C)) f1 s) + wp (compile (WHILE b DO C)) f2"
    by(simp only: wp_sup)
  finally show ?case .
qed auto 
 

lemma wp_linear': "deter C \<Longrightarrow> wp (compile C) ((f1::exp) + f2) =  wp (compile C) f1 + wp (compile C) f2"
  using wp_linear[where a=1] by auto


lemma wp0: "wp (compile C) (0::exp) = (0::exp)" 
proof (induct C)                                       
  case (While b C) 
  {
    fix i
    from While have "(chara b C 0 ^^ i) \<bottom> = 0"
      by (induct i) (auto simp: chara_def bot_ennreal)
  }
  then show ?case apply(subst wp_sup) by(auto simp add: wp_sup  ) 
qed auto

lemma wp_linearSum:
  fixes f :: "nat \<Rightarrow> state \<Rightarrow> ennreal"
  shows "deter C \<Longrightarrow> wp (compile C) (\<lambda>s. sum (\<lambda>i. f i s) {0..<n::nat}) = (\<lambda>s. sum (\<lambda>i. wp (compile C) (f i) s) {0..<n})"
proof (induct n)
  case 0
  have t: "(\<lambda>s. 0) = 0" by auto 
  show ?case by (auto simp: wp0 t)
next
  case (Suc n)
  have i: "(\<lambda>s. (\<Sum>i = 0..<n. f i s) + f n s) = ((\<lambda>s. (\<Sum>i = 0..<n. f i s)) + f n)" by auto
  thus ?case by (auto simp: wp_linear' Suc)
qed

lemma wp_le1:  "(\<And>s. f s \<le> 1) \<Longrightarrow> wp (compile C) f s \<le> 1"
proof (induct C arbitrary: f s) 
  case (Assign x)
  then show ?case by (auto simp add: measure_pmf.nn_integral_le_const)  
next                                    
  case (While b C) 
  { fix i
    from While have "(chara b C f ^^ i) \<bottom> \<le> 1"
      by (induct i) (auto simp: chara_def le_fun_def bot_ennreal)
  } note n=this  
  then show ?case by(subst wp_sup) (auto simp: le_fun_def SUP_le_iff)
qed (auto simp: le_infI2)



lemma awp_le1:  "(\<And>s. f s \<le> 1) \<Longrightarrow> awp (compile C) f s \<le> 1"
proof (induct C arbitrary: f s) 
  case (Assign x)
  then show ?case by (auto simp add: measure_pmf.nn_integral_le_const)   
next                                    
  case (While b C)  
  then have t: "\<And>s. awp (compile C) f s \<le> 1" by auto
  have "awp (compile (WHILE b DO C)) f \<le> 1" apply simp 
  proof (induct rule: lfp_induct)
    case 1
    then show ?case using mono_awp
      by (smt eq_iff le_funD le_funI mono_def)
  next
    case 2
    then show ?case using t While(2)
      by (simp add: While.hyps le_funI)  
  qed
  then show ?case by (auto dest: le_funD)
qed (auto simp: le_infI2)

end