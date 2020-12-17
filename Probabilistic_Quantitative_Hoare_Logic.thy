\<^marker>\<open>creator "Maximilian P.L. Haslbeck"\<close>
chapter \<open>Probabilistic Quantitative Hoare Logic\<close>
theory Probabilistic_Quantitative_Hoare_Logic
imports MDP_Semantics
begin

paragraph \<open>Summary\<close>

text \<open>This theory formalizes the probabilistic quantitative Hoare Logic from @{cite ngo2018bounded}.
  As a underlying semantics we use  @{term ert} -- the expected running time semantics of PGCL.
  This is a formalization of the theory in @{cite kaminskiESOP16} by Johannes Hölzl.

  We introduce a Hoare Logic to reason about the expected running time of PGCL programs.
  We prove soundness and completeness for the logic. Also, we come up with a VCG and prove it
  sound and complete.\<close>

paragraph \<open>Main Definitions\<close>

text \<open>
  \<^item> \<Turnstile> {P} c {Q}: a valid Hoare triple
  \<^item> @{text \<open>\<turnstile>\<^sub>Q {P} c {Q}\<close>}: the inference rules for the Hoare logic 
  \<^item> time, pre, vc: the functions for the VCG.
\<close>

paragraph \<open>Main Theorems\<close>

text \<open>
  \<^item> Hoare Logic soundness and completeness: hoareQ_sound hoareQ_complete
  \<^item> VCG soundness and completeness: vc_sound' vc_completeness
\<close>



section \<open>Hoare Logic\<close>
  
definition Qw ("\<Turnstile> {(1_)}/ (_)/ { (1_)}" 50) where "\<Turnstile> {P} c {Q} \<equiv> \<forall>s. P s \<ge> ert c Q s"  
  

lemma QwI: "ert c Q \<le> P \<Longrightarrow> \<Turnstile> {P} c {Q}"
  by(auto dest: le_funD simp: Qw_def)

lemma QwD: "\<Turnstile> {P} c {Q} \<Longrightarrow> ert c Q \<le> P"
  by(auto intro: le_funI simp: Qw_def)

lemma "ert c Q s \<ge> ert c 0 s"
  by (simp add: le_funD monoD mono_ert)
  
    
lemma ParRulew: assumes "Qw P c1 R" and "Qw P c2 R"
  shows "Qw P (Par c1 c2) R"
  using assms unfolding Qw_def apply auto done
    
definition lift :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ennreal" where "lift f s= (if f s then 0 else \<infinity>)" 
    
  
    
lemma IfRulew: assumes "Qw (%s. P s + lift b s) c1 R" and "Qw (%s. P s + lift (\<lambda>s. ~ b s) s ) c2 R"
  shows "Qw (\<lambda>s. 1+ P s) (If b c1 c2) R"
  apply(auto intro!: le_funI QwI) 
  subgoal using assms(1)[THEN QwD, unfolded lift_def, THEN le_funD] 
      by (metis add.right_neutral) 
    subgoal for s using assms(2)[unfolded Qw_def lift_def] 
      by (metis add.right_neutral)
  done
    
lemma HaltRulew: "Qw P (Halt) R" 
  by (simp add: Qw_def)
    
lemma SkipRulew: "Qw (%s. P s + 1) (Skip) P"
  by (simp add: Qw_def)
    
lemma EmptyRulew: "Qw P (Empty) P"
  by (simp add: Qw_def)
    
  
lemma SeqRulew': assumes "Qw P c1 Q" and "Qw Q c2 R"
  shows "Qw P (c1;;c2) R"
  using assms mono_ert[THEN monoD]
  apply(auto intro!: QwI dest!: QwD)
  using dual_order.trans by blast   

lemma SeqRulew: assumes "Qw P c1 Q" and "Qw Q c2 R"
  shows "Qw P (c1;;c2) R"
  unfolding Qw_def  
proof 
  fix s
  from assms have 1: "\<forall>s. P s \<ge> ert c1 Q s"
      and 2: "\<forall>s. Q s \<ge> ert c2 R s" unfolding Qw_def by auto
  from 2 have 3: "Q \<ge> ert c2 R" by (simp add: le_funI) 
      
  have "ert (c1;; c2) R s = ert c1 (ert c2 R) s" 
    apply simp done
  also have "\<dots> \<le> ert c1 Q s" using monoD[OF mono_ert 3]
    by (auto dest: le_funD) 
  also have "\<dots> \<le> P s" using 1 by auto
  finally 
  show "ert (c1;; c2) R s \<le> P s" .
qed

lemma ConseqRulew:
assumes "P' \<ge> P" "Q \<ge> Q'" "Qw P c Q"  
shows "Qw P' c Q'"
  unfolding Qw_def
proof 
  fix s
  from assms(3)[unfolded Qw_def] have "ert c Q s \<le> P s" by auto
      
  have "ert c Q' s \<le> ert c Q s" using monoD[OF mono_ert assms(2)]
    by (simp add: le_funD)  
  also have "\<dots> \<le> P s" using assms(3)[unfolded Qw_def] by auto
  also have "\<dots> \<le> P' s" using assms(1) 
    by (simp add: le_funD)  
  finally show "ert c Q' s \<le> P' s" .
qed
  
  
lemma chara:  "ert (While g c) R = (%x. 1 + (if g x then ert c (ert (While g c) R) x else R x))" 
proof -
  let ?g = "(\<lambda>W x. 1 + (if g x then ert c W x else R x))"
  have M: "mono ?g"
    apply rule
    by (simp add: le_funD le_funI monoD mono_ert)
      
  have A: "ert (While g c) R = lfp  ?g"
    apply simp done thm lfp_unfold
  also have "\<dots> = ?g (lfp ?g)"
    apply(rule lfp_unfold) by fact
  also have "\<dots> = ?g (ert (While g c) R)" unfolding A[symmetric] by simp
  finally show "ert (While g c) R = (%x. 1 + (if g x then ert c (ert (While g c) R) x else R x))" .  
qed
  
  
lemma WhileRulew: assumes "Qw (%s. P s + lift g s) c (%s. P s + 1)" 
  shows "Qw (%s. P s + 1) (While g c) (%s. P s +  lift (\<lambda>s. \<not>g s) s)" (is "Qw ?P1 ?W ?R")
    unfolding Qw_def
proof 
  fix s
  from assms have I: "\<And>s. P s + lift g s  \<ge> ert c (%s. P s + 1) s" unfolding Qw_def by auto
      
  let ?g = "(\<lambda>W x. 1 + (if g x then ert c W x else ?R x))"
    
   
  { fix s
    have "?g (%s. P s + 1) s \<le> (%s. P s + 1) s"
    proof (cases "P s < \<infinity>")
      case False
      then show ?thesis
        using top.not_eq_extremum by fastforce  
    next
      case True
      show ?thesis
      proof (cases "P s + lift g s < \<infinity>")
        case True
        then have g: "g s" unfolding lift_def
          using less_irrefl by fastforce 
        
        have "?g (%s. P s + 1) s = 1 + ert c (%s. P s + 1) s" using g by auto
        also have "\<dots> \<le> 1 + P s + lift g s"  using I by auto
        also have "\<dots> =  1 + P s" using g unfolding lift_def by auto       
        finally show ?thesis by simp
      next
        case False
        with True have "P s + lift (%s. \<not>g s) s  < \<infinity>" unfolding lift_def by auto
        then have g: "\<not>g s" unfolding lift_def
          using less_irrefl by fastforce 
        
        have "?g (%s. P s + 1) s = 1 + lift (\<lambda>s. \<not> g s) s + P s" using g by auto  
        also have "\<dots> = (%s. P s + 1) s" using g unfolding lift_def by auto
        finally show ?thesis by simp
      qed
    qed
  }
  then have "?g (%s. P s + 1) \<le> (%s. P s + 1)"
    by (simp add: le_fun_def)     
  then have "lfp ?g \<le> (%s. P s + 1)"
    by (simp add: lfp_lowerbound)      (* "park's theorem" *)
  then have "ert (While g c) ?R \<le> (%s. P s + 1)" by auto
  then show "ert (WHILE g DO c) ?R s \<le> P s + 1"
    by (simp add: le_fun_def)   
qed
    
lemma assign_easy:   "(\<And>i s. 1 + Q i \<le> p s) \<Longrightarrow> Qw p (Assign (\<lambda>s. return_pmf i)) Q"
  unfolding Qw_def by auto
      
lemma assign_easy':   "(\<And>s. 1 + Q (f s) \<le> p s) \<Longrightarrow> Qw p (Assign (\<lambda>s. return_pmf (f s))) Q"
  unfolding Qw_def by auto
  
    
lemma "(\<And>s. 1 + integral\<^sup>N (measure_pmf (u s)) Q \<le> P s) \<Longrightarrow> Qw P (Assign u) Q"
  unfolding Qw_def apply simp done
    
  
lemma assign: fixes u::"'a \<Rightarrow> 'a pmf"
  assumes I: "\<And>i. Qw (p i) (Assign (\<lambda>s. return_pmf i)) Q"
    (* p i can be set to infinity for values i that are not reached by u
       this simplifies showing I for it, while being easy to show P for it,
     *)
    and P: "\<And>s. P s = (\<lambda>x. \<integral>\<^sup>+i. p i s \<partial>u x) s" 
    shows  "Qw P (Assign u) Q"
  unfolding Qw_def
proof 
  fix s    
  from I have "\<And>s i . p i s \<ge> 1 +  (\<lambda>x. \<integral>\<^sup>+y. Q y \<partial>(\<lambda>s. return_pmf i) x) s" unfolding Qw_def by auto
  then have I: "\<And>s i . p i s \<ge> 1 + Q i" by simp
      
  have "ert (Assign u) Q s =  (\<lambda>x. \<integral>\<^sup>+y. 1 + Q y \<partial>u x) s"  by (auto simp: nn_integral_add)
  also have "\<dots> \<le> (\<lambda>x. \<integral>\<^sup>+y. p y s \<partial>u x) s" using I
    by (simp add: nn_integral_mono)
  also have "\<dots> = P s" using P by auto        
  finally show "ert (Assign u) Q s \<le> P s" .
qed      
  
 
lemma fixes s::nat
  shows "Qw (\<lambda>_. 1) (Assign (\<lambda>s. return_pmf (s+1))) (\<lambda>_. 0)"
  apply(rule assign[where p="%i s. (if i=s+1 then 1 else \<infinity>)"])
  subgoal for i unfolding Qw_def by simp
  subgoal by simp
  done
    
    
    
lemma fixes s::nat
  assumes [simp]: "0 \<le> p" "p \<le> 1" 
  shows "Qw (\<lambda>_. 1) (Assign (%s. map_pmf (%b. if b then s else s+1) (bernoulli_pmf p))) (\<lambda>_. 0)"
  apply(rule assign[where p="%i s. (if i=s \<or> i=s+1 then 1 else \<infinity>)"])
  subgoal for i unfolding Qw_def by simp
  subgoal for s apply simp using assms
    by (metis add.right_neutral add_diff_eq cancel_comm_monoid_add_class.diff_cancel diff_add_eq diff_ge_0_iff_ge ennreal_1 ennreal_plus) 
  done
    
    
    
    
subsection "inference rules"
  
  
type_synonym 'a qassn = "'a \<Rightarrow> ennreal" (* time bound *)
  
inductive
  hoareQ :: "'a qassn \<Rightarrow> 'a pgcl \<Rightarrow> 'a qassn \<Rightarrow> bool" ("\<turnstile>\<^sub>Q ({(1_)}/ (_)/ {(1_)})" 50)
where

Empty:  "\<turnstile>\<^sub>Q {P} Empty {P}"  |

Skip:  "\<turnstile>\<^sub>Q {\<lambda>s. 1 + P s} Skip {P}"  |

Halt:  "\<turnstile>\<^sub>Q {Q} Halt {P}"  |

Assign:  "(\<And>s. 1 + integral\<^sup>N (measure_pmf (u s)) Q \<le> P s)
               \<Longrightarrow> \<turnstile>\<^sub>Q {P} Assign u { Q }"  |

If: "\<lbrakk> \<turnstile>\<^sub>Q {\<lambda>s. P s + lift b s} c\<^sub>1 { Q};
       \<turnstile>\<^sub>Q {\<lambda>s. P s + lift (%s. \<not> b s) s} c\<^sub>2 { Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>Q {\<lambda>s. 1 + P s} If b c\<^sub>1 c\<^sub>2 { Q }"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>Q { P\<^sub>1 } c\<^sub>1 { P\<^sub>2 }; \<turnstile>\<^sub>Q {P\<^sub>2} c\<^sub>2 { P\<^sub>3 }\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>Q {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |

Par: "\<lbrakk> \<turnstile>\<^sub>Q { P } c\<^sub>1 { Q }; \<turnstile>\<^sub>Q {P} c\<^sub>2 { Q }\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>Q {P} Par c\<^sub>1 c\<^sub>2 {Q}"  |
 
While:
  "\<lbrakk>   \<turnstile>\<^sub>Q { %s. I s + lift b s } c { %t. I t + 1 }   \<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>Q {\<lambda>s. I s + 1 } WHILE b DO c {\<lambda>s.  I s + lift (%s. \<not> b s) s  }" |

conseq: "\<lbrakk> \<turnstile>\<^sub>Q {P}c{Q} ; P  \<le> P' ; Q'  \<le> Q  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>Q {P'}c{ Q'}"  
    
    
    

lemma hoareQ_sound: "\<turnstile>\<^sub>Q {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
proof (induction rule: hoareQ.induct) 
  case (If P b c\<^sub>1 Q c\<^sub>2)
  then show ?case using IfRulew by blast
next
  case (Seq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)  
  then show ?case using SeqRulew by blast
next
  case (While I b c)
  then show ?case  using WhileRulew by blast
next                       
  case (conseq P c Q P' Q')
  then show ?case using ConseqRulew by blast
qed  (auto simp: Qw_def)
    
    
  
subsection \<open>completeness\<close>
  
  
lemma hoareQ_complete_aux: "\<turnstile>\<^sub>Q {ert c Q} c {Q}"
proof (induct c arbitrary: Q) 
  case Skip
  then show ?case by (auto intro: hoareQ.Skip)  
next
  case (Par c1 c2)
  show ?case by (auto intro!: hoareQ.Par conseq[OF Par(1)] conseq[OF Par(2)] intro: le_funI) 
next
  case (If b c1 c2)
  show ?case by(auto intro!: hoareQ.If conseq[OF If(1)] conseq[OF If(2)] intro: le_funI simp: lift_def add_top)  
next
  case (While b c)
  show ?case 
    apply(rule conseq)
      apply(rule hoareQ.While[where I="%s. (if b s then ert c (ert (WHILE b DO c) Q) s else Q s)"])
      apply(rule conseq) 
        by (auto intro!: While[of "ert (WHILE b DO c) Q"] le_funI  simp del: ert.simps simp add: lift_def chara add_top) 
qed (auto intro: hoareQ.Halt hoareQ.Empty hoareQ.Assign hoareQ.Seq)
  
  
  
lemma hoareQ_complete: " \<Turnstile> {P} c {Q} \<Longrightarrow> \<turnstile>\<^sub>Q {P} c {Q}"
proof -
  assume "Qw P c Q"
  then have 1: "\<forall>s. P s \<ge> ert c Q s" unfolding Qw_def by auto
  show ?thesis
    apply(rule conseq)
      apply(rule hoareQ_complete_aux)
    using 1 by(auto intro: le_funI)
qed
  
lemma "\<Turnstile> {P} c {Q} \<longleftrightarrow> \<turnstile>\<^sub>Q {P} c {Q}"  
  using hoareQ_sound hoareQ_complete by auto    
    
lemma "\<Turnstile> {P} c {Q} \<longleftrightarrow> Ert Q c \<le> P"
  unfolding Qw_def le_fun_def by (simp add: ert_eq_Ert)
    
    
    
section "VCG"
  
datatype 'a apgcl = aEmpty
                 | aSkip
                 | aHalt
                 | aAssign "'a \<Rightarrow> 'a pmf"
                 | aSeq (left: "'a apgcl") (right: "'a apgcl") 
                 | aPar (left: "'a apgcl") (right: "'a apgcl")
                 | aIf "'a \<Rightarrow> bool" (left: "'a apgcl") (right: "'a apgcl")
                 | aWhile "'a \<Rightarrow> ennreal" "'a \<Rightarrow> bool" "'a apgcl"  
  
  
fun strip ::"'a apgcl \<Rightarrow> 'a pgcl" where
  "strip aEmpty = Empty" |
  "strip aSkip = Skip" |
  "strip aHalt = Halt" |
  "strip (aAssign u) = (Assign u)" |
  "strip (aSeq c1 c2) = Seq (strip c1) (strip c2)" |
  "strip (aPar c1 c2) = Par (strip c1) (strip c2)" |
  "strip (aIf b c1 c2) = If b (strip c1) (strip c2)" |
  "strip (aWhile I g c) = While g (strip c)"
  
  


fun pre :: "'a apgcl \<Rightarrow> 'a qassn \<Rightarrow> 'a qassn" where
"pre aEmpty Q = Q" |
"pre aSkip Q = (%s. 1 + Q s)" |
"pre aHalt Q = (%s. 0)" |
"pre (aAssign u) Q = 1 + (\<lambda>x. \<integral>\<^sup>+y. Q y \<partial>u x)" |
"pre (aSeq C\<^sub>1 C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (aPar c\<^sub>1 c\<^sub>2) Q = pre c\<^sub>1 Q \<squnion> pre c\<^sub>2 Q" |
"pre (aIf b C\<^sub>1 C\<^sub>2) Q = 1 + (\<lambda>s. (if b s then pre C\<^sub>1 Q s  else pre C\<^sub>2 Q s  ))" |
"pre (aWhile I b C) Q = (\<lambda>s. I s + 1)"  
  
 term ert 
  
   
fun vc :: "'a apgcl \<Rightarrow> 'a qassn \<Rightarrow> bool" where
"vc aSkip Q = True" |
"vc aHalt Q = True" |
"vc aEmpty Q = True" |
"vc (aAssign u) Q = True" |
"vc (aSeq C\<^sub>1 C\<^sub>2) Q = ((vc C\<^sub>1 (pre C\<^sub>2 Q)) \<and> (vc C\<^sub>2 Q) )" |
"vc (aPar C\<^sub>1 C\<^sub>2) Q = ((vc C\<^sub>1 Q) \<and> (vc C\<^sub>2 Q) )" |
"vc (aIf b C\<^sub>1 C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |  
"vc (aWhile I b C) Q =  ((\<forall>s. (pre C (\<lambda>s. I s + 1) s \<le> I s + lift b s) \<and> (Q s \<le> I s + lift (%s. \<not>b s) s)) \<and> vc C (%s. I s + 1))"

subsubsection "VCG soundness"
  
  
lemma vc_sound: "vc C Q \<Longrightarrow>  \<turnstile>\<^sub>Q {pre C Q} strip C { Q }"
proof (induct C arbitrary: Q) 
  case (aPar C1 C2)
  from aPar(3) have "vc C1 Q" "vc C2 Q" by auto
  with aPar(1,2) have 1: "\<turnstile>\<^sub>Q {pre C1 Q} strip C1 {Q}"
      and 2: "\<turnstile>\<^sub>Q {pre C2 Q} strip C2 {Q}" by auto  
  show ?case 
    using conseq[OF 1] conseq[OF 2] by (auto intro: hoareQ.Par simp add: le_funI)  
next
  case (aIf b C1 C2)
  from aIf(3) have "vc C1 Q" "vc C2 Q" by auto
  with aIf(1,2) have 1: "\<turnstile>\<^sub>Q {pre C1 Q} strip C1 {Q}"
      and 2: "\<turnstile>\<^sub>Q {pre C2 Q} strip C2 {Q}" by auto  
  show ?case apply(simp)
    apply(rule hoareQ.If[where P="%s. if b s then pre C1 Q s else pre C2 Q s" and Q="Q"])
    subgoal apply(rule conseq[OF 1]) apply (rule le_funI)
      subgoal for s apply(cases "b s") unfolding lift_def by (auto simp add: add_top) 
        by simp
    subgoal apply(rule conseq[OF 2]) apply (rule le_funI)
      subgoal for s apply(cases "b s") unfolding lift_def by (auto simp add: add_top) 
      by simp
    done
next
  case (aWhile I b C)
  from aWhile(2) have preT: "\<And>s. (pre C (\<lambda>s. I s + 1) s \<le> I s + lift b s)"
   and  preF: "\<And>s. Q s \<le> I s + lift (%s. \<not>b s) s" and vc: "vc C (%s. I s + 1)"  by auto
  from aWhile(1) vc have C: "\<turnstile>\<^sub>Q {pre C (\<lambda>s. I s + 1)} strip C {(\<lambda>s. I s + 1)}" by auto
    
  show ?case apply simp apply(rule conseq)
      apply(rule While)
      apply(rule conseq)
        apply(rule C) apply(rule le_funI)
       apply(rule preT)
      apply simp
     apply simp
      apply(rule le_funI)
      apply (rule preF)
    done
qed (auto intro: hoareQ.Skip hoareQ.Empty hoareQ.Halt hoareQ.Assign hoareQ.Seq )
 

lemma vc_sound': assumes "vc C Q " " P \<ge> pre C Q "" strip C = c " shows "  \<turnstile>\<^sub>Q {P} c { Q }" 
proof -
  have "\<turnstile>\<^sub>Q {P} strip C { Q }"
    apply(rule conseq)
      apply(rule vc_sound)
      apply fact+ by auto
  then show ?thesis using assms(3) by auto
qed
   
subsubsection "VCG completeness"
  
lemma pre_mono: assumes "\<And>s. P' s \<le> P s" 
  shows "\<And>s. pre C P' s \<le> pre C P s"
  using assms by (induct C arbitrary: P P', auto simp: nn_integral_mono le_supI2 le_supI1)    
     
  
lemma vc_mono: "P \<ge> Q \<Longrightarrow> vc C P \<Longrightarrow> vc C Q"
proof(induct C arbitrary: P Q)
  case (aSeq C1 C2)
  then show ?case apply (auto)
    by (metis le_fun_def pre_mono) 
next
  case (aWhile x1 x2 C)
  then show ?case apply (auto)
    by (metis le_fun_def order_trans)
qed auto
  
  
lemma vc_completeness: "\<turnstile>\<^sub>Q {P} c { Q } \<Longrightarrow>
  \<exists>C. vc C Q \<and> P \<ge> pre C Q \<and> strip C = c "
proof(induct rule: hoareQ.induct)
  case (Empty P)
  then show ?case apply(rule exI[where x=aEmpty]) by auto
next
  case (Skip P)
  then show ?case  apply(rule exI[where x=aSkip]) by auto
next
  case (Halt Q P)
  then show ?case  apply(rule exI[where x=aHalt]) by (auto simp add: le_funI) 
next
  case (Assign u Q P)
  show ?case apply(rule exI[where x="aAssign u"]) using Assign by (auto simp add: le_funI) 
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  then obtain C1 C2 where C1: "vc C1 Q \<and> pre C1 Q \<le> (\<lambda>a. P a + lift b a) \<and> strip C1 = c\<^sub>1"
      and C2: "vc C2 Q \<and> pre C2 Q \<le> (\<lambda>a. P a + lift (\<lambda>s. \<not> b s) a) \<and> strip C2 = c\<^sub>2" by auto
  show ?case apply(rule exI[where x="aIf b C1 C2"])
    using C1 C2 apply (auto simp add: le_funI) apply (rule le_funI)  unfolding lift_def 
     subgoal for x apply(cases "b x") apply auto
       apply (smt add.right_neutral le_fun_def)+ done done
next
  case (Seq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)
  then obtain C1 C2 where C1: "vc C1 P\<^sub>2  \<and> pre C1 P\<^sub>2 \<le> P\<^sub>1 \<and> strip C1 = c\<^sub>1"
      and C2: "vc C2 P\<^sub>3  \<and> pre C2 P\<^sub>3  \<le> P\<^sub>2  \<and> strip C2 = c\<^sub>2" by auto
  show ?case apply(rule exI[where x="aSeq C1 C2"])
      using C1 C2 apply (auto simp: vc_mono)   
      by (metis dual_order.trans le_fun_def pre_mono) 
next
  case (Par P c\<^sub>1 Q c\<^sub>2)
  then obtain C1 C2 where C1: "vc C1 Q \<and> pre C1 Q \<le> P \<and> strip C1 = c\<^sub>1"
      and C2: "vc C2 Q \<and> pre C2 Q \<le> P \<and> strip C2 = c\<^sub>2" by auto
  show ?case apply(rule exI[where x="aPar C1 C2"])
      using C1 C2 by (auto simp: le_fun_def)   
next
  case (While I b c)
  then obtain C where C: "vc C (\<lambda>a. I a + 1) \<and> pre C (\<lambda>a. I a + 1) \<le> (\<lambda>a. I a + lift b a) \<and> strip C = c" by auto
  show ?case apply(rule exI[where x="aWhile I b C"])
      using C by (auto simp: le_fun_def)   
next
  case (conseq P c Q P' Q')
  then obtain C where C: "vc C Q \<and> pre C Q \<le> P \<and> strip C = c" by blast
  show ?case apply(rule exI[where x=C])
    using C conseq(3,4) vc_mono pre_mono apply (auto)
    by (metis dual_order.trans le_fun_def pre_mono)   
qed 
  
  
section \<open>Examples\<close>
  
subsection "simple Random Walk"

definition Rdwalk :: "nat pgcl"
  where "Rdwalk = While (%x. x>0) (Assign (%x. map_pmf (\<lambda>b. if b then x+1 else x-1) (bernoulli_pmf (1/4))))"   

definition aRdwalk :: "(nat \<Rightarrow> ennreal) \<Rightarrow> nat apgcl" 
  where "aRdwalk I = aWhile I (%x. x>0) (aAssign (%x. map_pmf (\<lambda>b. if b then x+1 else x-1) (bernoulli_pmf (1/4))))"   


text \<open>Gather Information about the invariant\<close>
schematic_goal "vc (aRdwalk ?I) 0"    
  unfolding aRdwalk_def apply auto unfolding lift_def apply auto  
    apply (auto simp add: add_top) 
  apply(simp only: ennreal_numeral[symmetric] inverse_ennreal ennreal_1[symmetric] ) 
  oops
\<comment> \<open>ennreal 1 + ((?I (s + 1) + 1) * (1 / 4) + (?I (s - 1) + 1) *  (3 / 4)) \<le> ?I s\<close>

definition "eI (s::nat) = 4 * s + 1"
definition "I s = ennreal (eI s)"
lemma "0 < s \<Longrightarrow> eI \<ge> 0  \<Longrightarrow> 1 + ((I (Suc s) + 1) * ennreal (1 / 4) + (I (s - Suc 0) + 1) * ennreal (3 / 4)) \<le> I s"    
  unfolding I_def   apply auto
  apply(simp only: ennreal_numeral[symmetric] ennreal_plus[symmetric] ennreal_of_nat_eq_real_of_nat ennreal_mult[symmetric] ennreal_1[symmetric])
  apply(subst ennreal_plus[symmetric]) 
    apply (auto simp add: le_fun_def)[1] apply simp
  apply(subst ennreal_plus[symmetric]) 
    apply (auto simp add: le_fun_def)[1] apply simp 
  apply(subst ennreal_le_iff)
   apply (auto simp add: le_fun_def)[1]
  unfolding eI_def apply auto 
  by (simp only: add_divide_distrib)


lemma vc_Rdwalk: "vc (aRdwalk (%s. 4 * s + 1)) 0"    
  apply (simp add: aRdwalk_def) 
  by (auto intro: le_funI simp del: ennreal_plus ennreal_numeral ennreal_1
      simp: lift_def ennreal_mult[symmetric] ennreal_1[symmetric] ennreal_of_nat_eq_real_of_nat
      ennreal_numeral[symmetric] ennreal_plus[symmetric] add_divide_distrib)  


lemma derive: "\<turnstile>\<^sub>Q {pre (aRdwalk (%s. 4 * s + 1)) 0} Rdwalk {0}"        
  apply(rule vc_sound'[OF vc_Rdwalk])
  unfolding aRdwalk_def Rdwalk_def by auto


lemma "ert Rdwalk 0 s \<le> 1 + 4 * of_nat s + 1"
  using hoareQ_sound[OF derive, unfolded Qw_def aRdwalk_def, simplified]
  by auto 

        
        
        
subsubsection "geometric"
        
definition Geo :: "nat pgcl"
  where "Geo = While (%x. x=0) (Assign (%x. map_pmf (\<lambda>b. if b then (1::nat) else 0) (bernoulli_pmf (1/2))))"    
      
definition aGeo :: "(nat \<Rightarrow> ennreal) \<Rightarrow> nat apgcl"
  where "aGeo P  = aWhile P (%x. x=0) (aAssign (%x. map_pmf (\<lambda>b. if b then (1::nat) else 0) (bernoulli_pmf (1/2))))"    
      
  lemma "vc (aGeo (%s. ennreal (real (P s)))) 0"    
    unfolding aGeo_def apply auto unfolding lift_def apply (auto simp add: add_top) 
  apply(simp only: ennreal_numeral[symmetric] inverse_ennreal ennreal_1[symmetric])
  apply (subst  ennreal_plus[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_mult[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_plus[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_mult[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_plus[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_plus[symmetric])
    apply simp apply simp  
  apply (subst ennreal_le_iff) apply simp
      apply (simp only: distrib_right) apply auto oops
    (* left over: 2 + (real (P (Suc 0)) / 2 + real (P 0) / 2) \<le> real (P 0) *)
      
      
      
lemma vc_aGeo: "vc (aGeo (%s. if s=0 then 5 else 1)) 0"    
  unfolding aGeo_def apply auto unfolding lift_def apply (auto simp add: add_top ) 
  apply(simp only: ennreal_numeral[symmetric] inverse_ennreal )
  apply (subst  ennreal_mult[symmetric])
    apply simp apply simp  
  apply (subst  ennreal_mult[symmetric])
    apply simp apply simp apply simp done
       
lemma derive_aGeo: "\<turnstile>\<^sub>Q {pre (aGeo (%s. if s=0 then 5 else 1)) 0} Geo {0}"        
  apply(rule vc_sound'[OF vc_aGeo])
    unfolding aGeo_def Geo_def by auto
                  
lemma "ert Geo 0 s \<le> (if s=0 then 5 else 1) + 1"
using hoareQ_sound[OF derive_aGeo, unfolded Qw_def aGeo_def, simplified]
      by auto 
  
        
subsection "Random walk from Hölzl rough diamond"
        

definition random_walk :: "int pgcl"
where
  "random_walk =
    Seq
      (Assign (\<lambda>i. return_pmf 10))
      (While (\<lambda>i. 0 < i)
             (Assign (\<lambda>i. map_pmf (\<lambda>True \<Rightarrow> i + 1 | False \<Rightarrow> i - 1) (bernoulli_pmf (1/2)))))"        
        

definition arandom_walk :: "(int \<Rightarrow> ennreal) \<Rightarrow> int apgcl"
where
  "arandom_walk In =
    aSeq
      (aAssign (\<lambda>i. return_pmf 10))
      (aWhile In (\<lambda>i. 0 < i)
             (aAssign (\<lambda>i. map_pmf (\<lambda>True \<Rightarrow> i + 1 | False \<Rightarrow> i - 1) (bernoulli_pmf (1/2)))))"        
        
  
  
lemma "vc (arandom_walk IN) 0"
  unfolding arandom_walk_def apply (auto simp add: lift_def add_top)  oops
    
    
lemma "pre (arandom_walk IN) 0 s = 2 + IN 10"
  unfolding arandom_walk_def by auto
    
    
    
    
    
subsection "Example: Coupon Collector"
  
  
definition DetAssign :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a pgcl"
where
  "DetAssign f = Assign (\<lambda>s. return_pmf (f s))"
  
definition aDetAssign :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a apgcl"
where
  "aDetAssign f = aAssign (\<lambda>s. return_pmf (f s))"

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
  
definition acc  :: "(coupon_collector \<Rightarrow> ennreal) \<Rightarrow> (coupon_collector \<Rightarrow> ennreal) \<Rightarrow> nat \<Rightarrow> coupon_collector apgcl"
where
  "acc OI II N =
   aSeq (aDetAssign (\<lambda>_. \<lparr> cp = \<lambda>_. False, x = 0, i = 0 \<rparr>))
    (aWhile OI (\<lambda>s. x s < N) (
      (aWhile II (\<lambda>s. cp s (i s)) (
       aSeq (aAssign (\<lambda>s. map_pmf (\<lambda>i'. s\<lparr> i := i' \<rparr>) (pmf_of_set {0 ..< N}))) (
      aSeq (aDetAssign (\<lambda>s. s\<lparr> cp := (cp s)(i s := True)\<rparr>)) (
      aDetAssign (\<lambda>s. s\<lparr> x := x s + 1 \<rparr>)))))))"


  
  
lemma "0 < N \<Longrightarrow> vc (acc OI II N) 0"
  unfolding acc_def apply (auto simp add: aDetAssign_def lift_def add_top nn_integral_pmf_of_set) oops
  
term "(\<lambda>_. ennreal (real (2 + N * 4) + real (2 * N) * (\<Sum>i<N - 1. 1 / real (Suc i))))"
    
lemma "0 < N \<Longrightarrow> vc (acc OI II 10) 0"
  unfolding acc_def apply (auto simp add: aDetAssign_def lift_def add_top nn_integral_pmf_of_set)  
  oops
        
        
end