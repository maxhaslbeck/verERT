\<^marker>\<open>creator "Maximilian P. L. Haslbeck"\<close>
theory ERT_Of_IID_Loop_Classic
  imports PGCL_With_State IID_Loops
begin



text  \<open>This theory is OBSOLETE!

    It also tries to prove Theorem 4 from @{cite batzESOP18} and follows the paper
      more closely than the prove in Prove_Rule.\<close>



subsection "Misc"

lemma sum_shift_index_Suc: "(\<Sum>i = 0..<n. f (Suc i)) = sum f {1..<Suc n} "
proof -
  have "(sum (\<lambda>i. f (Suc i))   {0..<n})
        = (sum ((\<lambda>i. f i) o (\<lambda>n. n+1)) {0..<n})"
    by auto
  also have "\<dots> = (sum ((\<lambda>i. f i)) ((\<lambda>n. n+1) ` {0..<n}))"
    apply (rule sum.reindex[symmetric]) by auto
  also have "... = (sum (\<lambda>i. f i)   {1..<Suc n})" by simp
  finally show ?thesis .
qed

lemma fixes f :: "nat \<Rightarrow> ennreal"
  assumes "mono f"
  shows SUP_shift_mono: "(\<Squnion>n. f (n+1) ) = (\<Squnion>n. f n)"
proof -
  from assms have "mono (\<lambda>n. f (n+1))"
    unfolding mono_def by auto

  have *: "f ` UNIV = {f 0} \<union> (\<lambda>n. f (n+1)) ` UNIV"
    apply (auto simp: image_iff) by (metis not0_implies_Suc)
  have **: "Sup ((\<lambda>n. f (n+1)) ` UNIV) = (\<Squnion>n. f (n+1) )"
    by simp

  have k: "\<And>n. f 0 \<le> f (n+1)" using assms mono_def by auto

  have "(\<Squnion>n. f n) = Sup ({f 0} \<union> (\<lambda>n. f (n+1)) ` UNIV)"  apply(subst *) by simp
  also have "\<dots> = Sup {f 0} \<squnion> Sup ((\<lambda>n. f (n+1)) ` UNIV)" by auto
  also have "\<dots> = f 0  \<squnion> (\<Squnion>n. f (n+1) )" apply(subst **) by simp
  also have "\<dots> = (\<Squnion>n. f (n+1) )" using k
    by (meson Sup_upper2 UNIV_I antisym image_eqI le_sup_iff order_refl) 
  finally show ?thesis by simp
qed

lemma sum1: "suminf ((^) (1::ennreal)) = \<top>"  
proof -
  have i: "((^) (1::ennreal)) = (%_. 1)" by auto
  have ii: "(%_. 1::ennreal) sums \<infinity> \<longleftrightarrow> (\<lambda>x. ennreal (real x)) \<longlonglongrightarrow> \<infinity>"
    unfolding sums_def unfolding tendsto_def  by (auto simp: ennreal_of_nat_eq_real_of_nat)
  have iii: "(\<lambda>x. ennreal (real x)) \<longlonglongrightarrow> \<infinity>"
    using ennreal_of_nat_eq_real_of_nat of_nat_tendsto_top_ennreal by auto
  have *: "(%_. 1::ennreal) sums \<infinity>" using ii  iii by simp
  show ?thesis unfolding i using * sums_iff by auto
qed 

lemma incseqmult: "incseq (\<lambda>i. f i) \<Longrightarrow> (c::ennreal)\<ge>0 \<Longrightarrow> incseq (\<lambda>i. c * f i)" 
  by (auto simp add: mult_left_mono mono_def) 
 
lemma geometric_sums_ennreal: "(c::ennreal) < 1 \<Longrightarrow> (\<lambda>i. c ^ i) sums (1 / (1 - c))"
proof -
  assume "(c::ennreal) < 1"
  then obtain r where r: "c=ennreal r" "r\<ge>0" "r<1"
    by (metis ennreal_cases ennreal_less_one_iff not_le top.extremum) 

  have 1: "(\<lambda>i. ennreal ((^) r i)) = (\<lambda>i. c ^ i)" 
    by (auto simp add: r(1) ennreal_power r(2))   
  have 2: "ennreal (1 / (1 - r)) = (1 / (1 - c))"
    by (metis diff_gt_0_iff_gt divide_ennreal ennreal_1 ennreal_minus r(1) r(2) r(3) zero_le_one) 

  have R: "(^) r sums (1 / (1 - r)) "
    apply(rule geometric_sums)  using r by auto
  have "(\<lambda>i. ennreal ((^) r i)) sums ennreal (1 / (1 - r))"
    apply(subst sums_ennreal) using r R by auto
  then show "(\<lambda>i. c ^ i) sums (1 / (1 - c))"
    unfolding r 1 2 by simp    
qed

lemma suminf_geometric_ennreal: "(c::ennreal) < 1 \<Longrightarrow> suminf (\<lambda>i. c ^ i) = (1 / (1 - c))" 
    by (rule sums_unique[symmetric]) (rule geometric_sums_ennreal)


subsection "Lemmas about Sup"

lemma fixes g ::exp and f :: "nat \<Rightarrow> exp"
  shows SUP_mult_left_ennreal_fun: "(\<Squnion>i. g * (f i) ) = g * (\<Squnion>i. (f i))"
  by(auto simp: SUP_mult_left_ennreal SUP_image)

lemma Sup_If:
  fixes g :: "nat \<Rightarrow> exp" and f :: "exp"
  assumes "A \<noteq> {}"
  shows "(\<Squnion>n\<in>A. (\<lambda>s. if b s then g n s else f s)) = (\<lambda>s. if b s then (\<Squnion>n\<in>A. g n s) else f s)"
proof -
  have "\<And>s. A \<noteq> {} \<Longrightarrow> (\<Squnion>n\<in>A. f s) = f s" by auto
  have "(\<Squnion>n\<in>A. (\<lambda>s. if b s then g n s else f s)) = (\<lambda>s. (\<Squnion>n\<in>A.  if b s then g n s else f s))" 
    by (auto simp: SUP_image)
  also have "\<dots> = (\<lambda>s. if b s then (\<Squnion>n\<in>A. g n s) else f s)"
    apply(rule ext) using assms by auto
  finally show ?thesis .
qed



lemma wp_missing: "wp (compile C) (\<lambda>s. if b s then 1 else 0) s = 1
      \<Longrightarrow> wp (compile C) (\<lambda>s. if b s then 0 else f s) s = 0"
  (* proof in appendix A4. of Batz Paper argues via the semantics
      of the program C
  *) (*
proof (induct C arbitrary: s)  
  case (Assign x1 x2)
  then show ?case sorry
next
  case (Seq C1 C2)
  have "wp (compile (C1;; C2)) (\<lambda>s. if b s then 1 else 0) s = 1" apply auto
    sorry
  have a: "\<And>x. wp (compile C2) (\<lambda>s. if b s then 1 else 0) x = 1"
  proof (rule ccontr)
    fix x
    assume " wp (compile C2) (\<lambda>s. if b s then 1 else 0) x \<noteq> 1"
    with wp_le1 have "wp (compile C2) (\<lambda>s. if b s then 1 else 0) x < 1"
      by (simp add: order.not_eq_order_implies_strict) 
    with Seq(3) mono_wp have "False" (* no !*) 
  qed

  have 2: "wp (compile C2) (\<lambda>s. if b s then 0 else f s)  = 0"
    apply(rule) apply simp apply(rule Seq(2)) by (fact a)
  show ?case by(auto simp: 2 wp0)
next 
  case (While x1 C)
    then show ?case sorry
qed auto *) sorry



subsection "Proof of the new Prove Rule"



lemma assumes "fiid C b f" and "n>0"
  shows lemma2a: "
        wp (compile C) (\<lambda>s. if b s
               then wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s
                       * sum (\<lambda>i. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ i) {0..<n-1}
               else 0) = 
          wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) * (%s. sum (\<lambda>i. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ i) {1..<n})  "
 (is "?L = ?R") 
proof -
  let ?W = "wp (compile C) (\<lambda>s. if b s then 1 else 0)"
  let ?wnf = "wp (compile C) (\<lambda>s. if \<not>b s then f s else 0)"

  { 
    fix s i (* here is the meat of it! *)
    have t: "((\<lambda>s. if \<^bold>\<not> b s then 1 else 0) * f)  = (\<lambda>s. if b s then 0 else f s)" by auto

    from assms(1) have a: "unaffected ?W C"
                and    b:  "unaffected (wp (compile C) (\<lambda>s. if b s then 0 else f s)) C"
      unfolding fiid_def lift2_def t by auto
    have 2: " (wp (compile C) (%s. if b s
               then wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s * ((?W s) ^ i) else 0) ) s
      =   wp (compile C) (lift2 b * (\<lambda>s. wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s * ?W s ^ i)) s"
         (is "?A = ?B")
      by(simp add: lift2_fold)
    also have "\<dots> = wp (compile C) ( (lift2 b *  ?wnf) * (\<lambda>s. ?W s ^ i)) s"  
    proof -
      have k: "\<And>i. (lift2 b * (\<lambda>s. ?wnf s * ?W s ^ i))
        = ( (lift2 b *  ?wnf) * (\<lambda>s. ?W s ^ i))" by (auto simp add: mult.assoc)    
      show ?thesis by(simp only: k)
    qed   
    also have "\<dots> = (wp (compile C) (lift2 b * wp (compile C) (\<lambda>s. if \<not>b s then f s else 0)) * 
            (\<lambda>s. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ i)) s" 
      by (simp add: a scale_unaffected_expectations_iter) 
    also have "\<dots> = (?W * wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) * (\<lambda>s. (?W s) ^ i)) s"
    proof -
      (* second important step *)
      have l: "(\<lambda>s. if \<not>b s then f s else 0) = (\<lambda>s. if b s then 0 else f s)" by auto
      show ?thesis by(simp only: l lift2_def scale_unaffected_expectations_right[OF b]) 
    qed    
    also have "\<dots> = (wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) * ?W * (\<lambda>s. (?W s) ^ i)) s" by (auto simp add: mult.commute) 
    also have "\<dots> = (wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) * (\<lambda>s. (?W s) ^ (i+1))) s" (is "_ = ?D")
      by (auto simp add: mult.assoc)
    finally have "?A=?D" .
  } note 2=this


  { fix n :: nat and s
    assume "n>0"
    then obtain n' where n': "n-1 = n'" "n = Suc n'"
      using Suc_pred' by blast     
    have "(\<Sum>i = 0..<n - 1. ?W s ^ (i + 1)) = sum ((^) (?W s)) {1..<n} "
      apply(simp only: n' diff_Suc_1 Suc_eq_plus1[symmetric]) by(rule sum_shift_index_Suc)
  } note 3=this
 
  have "(\<lambda>s. if b s then ?wnf s * sum (\<lambda>i. ?W s ^ i) {0..<n-1} else 0) 
        = (\<lambda>s. sum (\<lambda>i. if b s then ?wnf s * ?W s ^ i else 0) {0..<n-1})" (is "_=?L'") 
    by (auto simp add: sum_distrib_left)
  then
  have "?L = wp (compile C) ?L'" by simp
  also have "\<dots> = (\<lambda>s. sum (\<lambda>i. wp (compile C) (%s. if b s
               then ?wnf s * ?W s ^ i else 0) s) {0..<n-1})"
    by(rule wp_linearSum)
  also have "\<dots> = (\<lambda>s. sum (\<lambda>i. (?wnf * (\<lambda>s. ?W s ^ (i+1)) ) s)  {0..<n-1})"
    by(simp only: 2) 
  also have "\<dots> = (\<lambda>s. ?wnf s  * (sum (\<lambda>i. ?W s ^ (i+1))   {0..<n-1}))"
    by(auto simp: sum_distrib_left)
  also have "\<dots> = (\<lambda>s. ?wnf s  * (sum (\<lambda>i. ?W s ^ i) {1..<n}))"
    by (simp only: 3[OF assms(2)])
  finally show ?thesis by auto
qed

lemma sum_extract: "n<m \<Longrightarrow> sum (g::nat\<Rightarrow>ennreal) {Suc n..<m} + g n = sum g {n..<m}"
  apply(simp only: sum_head_upt_Suc) by auto

lemma lemma2: fixes C :: spgcl 
  assumes "fiid C b f"
  shows "1\<le>n \<Longrightarrow>
       ((chara b C f) ^^ n) (\<bottom>::exp) =
          (\<lambda>s. if b s
               then wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s
                       * sum (\<lambda>i. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ i) {0..<n-1}
               else f s)"
proof(induction n rule: Nat.dec_induct)
  case base
  have t: "(\<lambda>a. 0) = (0::exp)" by auto
  show ?case
    by (auto simp add: chara_def bot0 t wp0 intro!: sum.empty)   
next
  case (step n)
  let ?C = "chara b C f"
  let ?W = "wp (compile C) (\<lambda>s. if b s then 1 else 0)"
  let ?F = "wp (compile C) (\<lambda>s. if \<not> b s then f s else 0)"
  let ?I = "%s. ?F s * sum ((^) (?W s)) {0..<n - 1}"
  have i: "(\<lambda>s. if b s then ?I s else f s) = lift2 b * ?I + lift2 (\<lambda>s. \<not> b s) * f"
    unfolding lift2_def by auto

  have "(?C ^^ Suc n) \<bottom> = ?C ((?C ^^ n) \<bottom>)" by auto
  also have "\<dots> = ?C ((\<lambda>s. if b s then ?I s else f s))" by(simp only: step)
  also have "\<dots> = lift2 b * (wp (compile C) (lift2 b * ?I) + wp (compile C) (lift2 (\<lambda>s. \<not> b s) * f))
                   + lift2 (\<lambda>s. \<not> b s) * f" (is "?D=?E") by (simp add: chara_alt i wp_linear')
  also
  have 1: "wp (compile C) (lift2 b * ?I) = wp (compile C) (\<lambda>s. if \<not> b s then f s else 0) 
          * (\<lambda>s. sum ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) {1..<n})" (is "_=?WI")
    unfolding lift2_fold[symmetric] apply(rule lemma2a)  using step assms by auto
  have 2: "(wp (compile C) (lift2 (\<lambda>s. \<not> b s) * f))
          * (\<lambda>s. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ 0) = wp (compile C) (lift2 (\<lambda>s. \<not> b s) * f)"
    by auto
  have "?E = lift2 b * (?WI + (wp (compile C) (lift2 (\<lambda>s. \<not> b s) * f))
          * (\<lambda>s. (wp (compile C) (\<lambda>s. if b s then 1 else 0) s) ^ 0)) +
    lift2 (\<lambda>s. \<not> b s) * f" by (simp only: 1 2)
  also have "\<dots> =  lift2 b * (?F * ((\<lambda>s. sum ((^) (?W s)) {1..<n}) +  (\<lambda>s. ?W s ^ 0)))
                   + lift2 (\<lambda>s. \<not> b s) * f" (is "_=?g")
    by (simp add: distrib_left lift2_fold[symmetric]) 
  also
  from step have z: "((\<lambda>s. sum ((^) (?W s)) {1..<n}) +  (\<lambda>s. ?W s ^ 0) 
        =  (\<lambda>s. sum ((^) (?W s)) {0..<n}))"
    by (auto simp del: power.power_0 intro!: ext sum_extract) 
  have "?g = lift2 b * (?F * ((\<lambda>s. sum ((^) (?W s)) {0..<n}))) + lift2 (\<lambda>s. \<not> b s) * f"
    by(simp only: z) 
  also have "\<dots> = (\<lambda>s. if b s then ?F s * sum ((^) (?W s)) {0..<Suc n - 1} else f s)"
    by (auto simp: lift2_def)
  finally show ?case .
qed

lemma assumes "fiid C b f"  
  shows thm3: (* weakest-preexpectation of f-iid loops *)
    "wp (compile (While b C)) f =
         (\<lambda>s. if b s 
              then (wp (compile C) (\<lambda>s. if b s then 0 else f s) s) / (1 - wp (compile C) (\<lambda>s. if b s then 1 else 0) s)
              else f s)"
proof -
  let ?I = "(wp (compile C) (\<lambda>s. if b s then 1 else 0))"
  let ?Li = "(%n s. wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s
                       * sum (\<lambda>i. (?I s) ^ i) {0..<n-1})"
  let ?L = "(%n. (\<lambda>s. if b s
               then ?Li n s
               else f s))"

  have ttt: "{1..} = {x::nat. x>0}" by auto 

  have tt: "(\<lambda>i::nat. ((chara b C f) ^^ i) \<bottom>) ` {1..}
      = ?L ` {1..}" using  lemma2[OF assms] by force
  have "(chara b C f ^^ 0) \<bottom> = 0" unfolding bot0 by simp
  have t: "({0::nat}\<union>{1..}) = UNIV" by auto

  have "wp (compile (While b C)) f
          = (\<Squnion>i. ((chara b C f) ^^ i) \<bottom>)" using wp_sup by auto (* by definition 2 *)
  also have "\<dots> = SUPREMUM ({0}\<union>{1..}) (\<lambda>i::nat. ((chara b C f) ^^ i) \<bottom>)"
    unfolding t by auto
  also have "\<dots> =  (\<Squnion>i\<in>{1..}. (chara b C f ^^ i) \<bottom>)"  by auto
  also have "\<dots> = (\<Squnion>n\<in>{1..}. ?L n)" unfolding tt by simp
  also have "\<dots> = (\<Squnion>n\<in>{x. 0 < x}. ?L n)" unfolding ttt by auto
  also have "\<dots> = (\<lambda>s. if b s
               then wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s
                       * suminf ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s))
               else f s)" (* pull the limit inwards *)
  proof -
    have 1: "(\<Squnion>n\<in>{x. 0 < x}. ?L n) = (\<lambda>s. if b s then (\<Squnion>n\<in>{x. 0 < x}. ?Li n s) else f s)"
      apply (rule Sup_If) by auto
     
    have 2: "\<And>s. (\<Squnion>n\<in>{x. 0 < x}. ?Li n s) = wp (compile C) (\<lambda>s. if \<not>b s then f s else 0) s
                * (\<Squnion>n\<in>{x. 0 < x}. sum (\<lambda>i. (?I s) ^ i) {0..<n-1})"
      by (simp add: SUP_mult_left_ennreal) 
    { fix s
      have *: "(\<lambda>n. sum (\<lambda>i. (?I s) ^ i) {0..<n-1}) ` {x::nat. 0 < x}
            =  (\<lambda>n. sum (\<lambda>i. (?I s) ^ i) {0..<n}) ` UNIV"
        using image_iff by fastforce 
      have t: "\<And>n. {0::nat..<n} = {..<n}" by auto
      have "(\<Squnion>n\<in>{x. 0 < x}. sum (\<lambda>i. (?I s) ^ i) {0..<n-1})
          = suminf (\<lambda>i. (?I s) ^ i)" 
        unfolding * by(simp only: t suminf_eq_SUP)       
    } note 3 = this

    show ?thesis unfolding 1 2 3 by simp
  qed
  also have "\<dots> = (\<lambda>s. if b s 
              then (wp (compile C) (\<lambda>s. if b s then 0 else f s) s) / (1 - wp (compile C) (\<lambda>s. if b s then 1 else 0) s)
              else f s)"
    apply(rule ext) subgoal for s 
    proof (cases "b s")
      case b: True 
      have kk: "(\<lambda>s. if \<not> b s then f s else 0) = (\<lambda>s. if b s then 0 else  f s)" by auto

      show ?thesis
      proof (cases "?I s < 1")
        case True (* use closed form of geometric series *)   
        have k: "(\<Sum>n. (?I s) ^ n) = 1 / (1 - ?I s)" using True 
          by (rule suminf_geometric_ennreal)
        from b True show ?thesis by (auto simp: k kk ennreal_times_divide)
      next
        case False
        with wp_le1 have i: "?I s = 1"
          by (metis (mono_tags, lifting) eq_refl linorder_cases not_le zero_le_one)        
        then have n: "wp (compile C) (\<lambda>s. if b s then 0 else f s) s = 0"
          by(rule wp_missing)
        from b show ?thesis by (simp add: kk i n)
      qed
    qed simp
    done
  finally show ?thesis .
qed

lemma "(0::ennreal) / 0 = 0" by simp
lemma "(1::ennreal) / 0 = \<infinity>" by simp


lemma lemma4: 
  assumes
    "fiid C b 0"
  and
    "wp (compile C) 1 = 1"
  and
    "unaffected (ert (compile C) 0) C"
  shows 
    "n\<ge>1 \<Longrightarrow> ((charaErt b C 0) ^^ n) (\<bottom>::exp) = (\<lambda>s. 1 + (if b s then ert (compile C) 0 s * sum (\<lambda>i. wp (compile C) (lift2 b) s ^ i) {0..<n}
                                                  + sum (\<lambda>i. wp (compile C) (lift2 b) s ^ i) {0..<n-1}
                                        else 0))"
proof(induction n rule: Nat.dec_induct)
  case base
  have t: "(\<lambda>a. 0) = (0::exp)" by auto
  show ?case  
    by (auto simp add: charaErt_def t bot0) 
next
  case (step n)
  let ?C = "charaErt b C 0"
  let ?W = "wp (compile C) (lift2 b)"
  let ?E= "ert (compile C) 0"
  let ?I = "(\<lambda>s. 1 + (if b s then ?E s * sum ((^) (?W s)) {0..<n} + sum ((^) (?W s)) {0..<n- 1} else 0))"
 

  have "unaffected (wp (compile C) (\<lambda>s. if b s then 1 else 0)) C"
    using assms  by (simp add: lift2_def fiid_def)
  then have pullout: "\<And>c s i. wp (compile C) (c * (%s. (?W s) ^ i)) s 
      = (wp (compile C) c * (%s. (?W s) ^ i)) s"
     by (auto simp: scale_unaffected_expectations_iter lift2_def)  

  { fix n
    have 1: "lift2 b * ?E * (\<lambda>s. sum ((^) (?W s)) {0..<n})
        = (\<lambda>s. sum (\<lambda>i. lift2 b s * ?E s * (?W s) ^ i) {0..<n})"
      by (auto simp: sum_distrib_left)

    have 2: "\<And>i. (%s. lift2 b s * ?E s * (?W s) ^ i) = ((lift2 b * ?E) * (%s. (?W s) ^ i))"
      by (auto simp add: mult.assoc)    

    have 3: "wp (compile C) (lift2 b * ?E) = wp (compile C) (lift2 b) * ?E"
      apply(rule scale_unaffected_expectations_right) by (fact assms(3))
 
    have 4: "\<And>s. (\<lambda>i. (wp (compile C) (lift2 b) * ?E * (%s. (?W s) ^ i)) s)
            = (\<lambda>i. ?E s * ((%s.  (?W s) ^ Suc i)) s)"
        by (auto simp add: mult.commute mult.left_commute) 

    have "wp (compile C) (lift2 b * ?E * (\<lambda>s. sum ((^) (?W s)) {0..<n}))
            = wp (compile C) (\<lambda>s. sum (\<lambda>i. lift2 b s * ?E s * (?W s) ^ i) {0..<n})"
      by(simp only: 1)
    also have "\<dots> = (%s. sum (\<lambda>i. wp (compile C) (%s. lift2 b s * ?E s * (?W s) ^ i) s) {0..<n})"
      by(rule wp_linearSum)
    also have "\<dots> = (%s. sum (\<lambda>i. wp (compile C) ((lift2 b * ?E) * (%s. (?W s) ^ i)) s) {0..<n})"
      by(simp only: 2)
    also have "\<dots> = (%s. sum (\<lambda>i. (wp (compile C) (lift2 b * ?E) * (%s. (?W s) ^ i)) s) {0..<n})"
      by(simp only: pullout)
    also have "\<dots> = (%s. sum (\<lambda>i. (wp (compile C) (lift2 b) * ?E * (%s. (?W s) ^ i)) s) {0..<n})"
      by(simp only: 3)
    also have "\<dots> = (%s. sum (\<lambda>i. ?E s * ((%s.  (?W s) ^ Suc i)) s) {0..<n})"
      by(simp only: 4) 
    also have "\<dots> = ?E * (\<lambda>s. sum (\<lambda>i. (?W s) ^ Suc i) {0..<n} )"
      by(auto simp add: sum_distrib_left)   
    also have "\<dots> = ?E * (\<lambda>s. sum (\<lambda>i. (?W s) ^ i) {1..<Suc n} )"
      by (simp only: sum_shift_index_Suc)
    finally have "wp (compile C) (lift2 b * ?E * (\<lambda>s. sum ((^) (?W s)) {0..<n}))
          = ?E * (%s. sum ((^) (?W s)) {1..<Suc n})" .
  } note eq6=this

  { fix n
    have 1: "(lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n}))
        =  ((\<lambda>s. sum (\<lambda>i. lift2 b s * (?W s) ^ i) {0..<n}))" 
      by (auto simp: sum_distrib_left)

    have 2: "\<And>s. (\<lambda>i. (?W * (%s. (?W s) ^ i)) s) = (\<lambda>i. (?W s) ^ Suc i)"
      apply rule by auto

    have "wp (compile C) (lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n}))
            = wp (compile C) ((\<lambda>s. sum (\<lambda>i. lift2 b s * (?W s) ^ i) {0..<n}))"
      by(simp only: 1)
    also have "\<dots> = (%s. sum (\<lambda>i. wp (compile C) (%s. lift2 b s * (?W s) ^ i) s) {0..<n})"
      by(rule wp_linearSum)
    also have "\<dots> = (%s. sum (\<lambda>i. wp (compile C) (lift2 b * (\<lambda>s. (?W s) ^ i)) s) {0..<n})"
      by (auto simp add: times_fun_def)
    also have "\<dots> = (%s. sum (\<lambda>i. (?W * (%s. (?W s) ^ i)) s) {0..<n})"
      by (simp only: pullout)
    also have "\<dots> = (%s. sum (\<lambda>i. (?W s) ^ Suc i) {0..<n})"
      by (simp only: 2)
    also have "\<dots> = (%s. sum (\<lambda>i. (?W s) ^ i) {1..<Suc n})"
      by (simp only: sum_shift_index_Suc)
    finally have "wp (compile C) (lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n}))
          = (%s. sum ((^) (?W s)) {1..<Suc n})" .
  } note eq7=this

  have "(?C ^^ Suc n) \<bottom> = ?C ((?C ^^ n) \<bottom>)" by auto
  also have "\<dots> = ?C ?I" by(simp only: step)
  also have "\<dots> = 1 + (lift2 b) * ert (compile C) ?I"
    unfolding charaErt_alt by simp
  also have "\<dots> =  1 + (lift2 b) * (ert (compile C) 0 + wp (compile C) ?I)"
    using decompose_ert by metis (* paper has different order of the last two steps, but does not matter! *)
  also have "\<dots> = 1 + lift2 b * (ert (compile C) 0
               + wp (compile C) (\<lambda>s. 1 + (lift2 b * (\<lambda>s. ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n}
                                                                 + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1})) s))"
    unfolding lift2_def apply clarsimp
    proof -
      have "1 + (\<lambda>f. if b f then 1 else 0) * (ert (compile C) 0 + wp (compile C) (\<lambda>f. 1 + (if b f then ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - 1} else 0))) = 1 + (\<lambda>f. if b f then 1 else 0) * (ert (compile C) 0 + wp (compile C) (\<lambda>f. 1 + (if b f then 1 else 0) * (ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - Suc 0}))) \<or> (\<forall>f. 1 + (if b f then ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - 1} else 0) = 1 + (if b f then 1 else 0) * (ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - Suc 0}))"
        by simp
      then show "1 + (\<lambda>f. if b f then 1 else 0) * (ert (compile C) 0 + wp (compile C) (\<lambda>f. 1 + (if b f then ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - 1} else 0))) = 1 + (\<lambda>f. if b f then 1 else 0) * (ert (compile C) 0 + wp (compile C) (\<lambda>f. 1 + (if b f then 1 else 0) * (ert (compile C) 0 f * sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n} + sum ((^) (wp (compile C) (\<lambda>f. if b f then 1 else 0) f)) {0..<n - Suc 0})))"
        by presburger
    qed  (*refine *)
  also have "\<dots> = 1 + lift2 b * (ert (compile C) 0 + wp (compile C) (\<lambda>s. 1 + (lift2 b * (\<lambda>s. ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n}) + lift2 b * (%s. sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1})) s))"
    by (simp add: distrib_left) 
  also
  let ?A = "lift2 b * ert (compile C) 0 * (%s. sum ((^) (wp (compile C) (lift2 b) s)) {0..<n})"
  let ?B = "(lift2 b * (%s. sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1}))"
  
  have "\<dots> = 1 + lift2 b * (ert (compile C) 0 + wp (compile C) ((\<lambda>s. 1) + ?A + ?B))" (is "_= 1 + lift2 b * ?R") 
  proof -
    have t: "(lift2 b * (\<lambda>s. ert (compile C) 0 s * sum ((^) (?W s)) {0..<n}) + lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n - 1}))
        = (lift2 b * ert (compile C) 0 * (\<lambda>s. sum ((^) (?W s)) {0..<n}) + lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n - 1}))"
      apply(rule) by (simp add: mult.assoc)
    have tt: "(\<lambda>s. 1 + (lift2 b * (\<lambda>s. ert (compile C) 0 s * sum ((^) (?W s)) {0..<n}) + lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n - 1})) s)
      = ((\<lambda>s. 1) + lift2 b * ert (compile C) 0 * (\<lambda>s. sum ((^) (?W s)) {0..<n}) + lift2 b * (\<lambda>s. sum ((^) (?W s)) {0..<n - 1}))" 
      apply(simp only: t) by auto
    show ?thesis  by(simp only: tt) 
  qed
  also 
  { have "wp (compile C) ((\<lambda>s. 1) + ?A + ?B)
            = wp (compile C) 1 + wp (compile C) ?A + wp (compile C) ?B"
    apply (simp only: wp_linear') by (metis one_fun_apply)  \<comment> linearity
    
    also have "\<dots> = 1 + ?E * (%s. sum ((^) (?W s)) {1..<Suc n}) + (%s. sum ((^) (?W s)) {1..<n})"
      apply(simp only: assms(2) eq6 eq7) using step by simp
    finally have k: "wp (compile C) ((\<lambda>s. 1) + ?A + ?B) = 1 + ?E * (%s. sum ((^) (?W s)) {1..<Suc n}) + (%s. sum ((^) (?W s)) {1..<n})"
      .
    have "?R =
          (?E + ?E * (%s. sum ((^) (?W s)) {1..<Suc n})) + (1 + (%s. sum ((^) (?W s)) {1..<n}))"
      apply(simp only: k) by auto
    also have "\<dots> = (?E * (1 + (%s. sum ((^) (?W s)) {Suc 0..<Suc n}))) + (1 + (%s. sum ((^) (?W s)) {Suc 0..<n}))"
      by (simp add: distrib_left) 
    also have "\<dots> = (?E * ((%s. ?W s ^ 0 + sum ((^) (?W s)) {Suc 0..<Suc n}))) + ((%s. ?W s ^ 0 + sum ((^) (?W s)) {Suc 0..<n}))"
      by auto
    also have "\<dots> = (?E * ((%s. sum ((^) (?W s)) {0..<Suc n}))) + ((%s. sum ((^) (?W s)) {0..<n}))"       
      using step by(simp only: sum_head_upt_Suc[symmetric]) 
    finally have "?R = (?E * ((%s. sum ((^) (?W s)) {0..<Suc n}))) + ((%s. sum ((^) (?W s)) {0..<n}))" .
  } note k=this
  have "1 + lift2 b * ?R = 1 + lift2 b * ((?E * ((%s. sum ((^) (?W s)) {0..<Suc n}))) + ((%s. sum ((^) (?W s)) {0..<n})))"
    by(simp only: k)
  also have "\<dots> = (\<lambda>s. 1 + (if b s then ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<Suc n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<Suc n - 1} else 0))"
    by (auto simp: lift2_def)
  finally  show ?case .
qed 


lemma hauptnenner: "(eb::ennreal) / ea + e / ea = (eb + e) / ea"
 by (metis (no_types) comm_semiring_class.distrib ennreal_times_divide mult.right_neutral)
 

theorem thm4: assumes
  "fiid C b f" and
  "wp (compile C) 1 = 1" (* loop body terminates almost-surely *)
  "unaffected (ert (compile C) 0) C"
shows "ert (compile (While b C)) f = (%s. 1 + (if b s then (1 + ert (compile C) (\<lambda>s. if b s then 0 else f s) s)
                                                               /  
                                                            (1- (wp (compile C) (\<lambda>s. if b s then 1 else 0)) s)
                                                      else f s))" (is "?E f = ?R f")
proof -

  have k: "(\<lambda>s. if b s then 0 else 0 s) = 0" "\<And>a. 0 a = 0" by auto
  have 2: "fiid C b 0" 
    apply (auto simp: unaffected_def Vars_def fiid_def k wp0)
    using assms(1) fiid_def unaffaccted_fun_upd by fastforce 


  let ?I = "(wp (compile C) (\<lambda>s. if b s then 1 else 0))"
  have 1: "?E 0 = ?R 0"
  proof -
    (* analogous to thm3 *)
    let ?L = "(\<lambda>n s. 1 + (if b s then ert (compile C) 0 s * sum (\<lambda>i. wp (compile C) (lift2 b) s ^ i) {0..<n}
                                                  + sum (\<lambda>i. wp (compile C) (lift2 b) s ^ i) {0..<n-1}
                                        else 0))"
    have t: "({0::nat}\<union>{1..}) = UNIV" by auto
    have tt: "(\<lambda>i::nat. ((charaErt b C 0) ^^ i) \<bottom>) ` {1..}
        = ?L ` {1..}"  using  lemma4[OF 2 assms(2,3)] by force 
    have ttt: "{1..} = {x::nat. x>0}" by auto

    thm ert_sup
    have "ert (compile (While b C)) 0 = (\<Squnion>i. (charaErt b C 0 ^^ i) \<bottom>)" apply(subst ert_sup) by auto   
    also have "\<dots> = SUPREMUM ({0}\<union>{1..}) (\<lambda>i::nat. ((charaErt b C 0) ^^ i) \<bottom>)"
      unfolding t by auto
    also have "\<dots> =  (\<Squnion>i\<in>{1..}. ((charaErt b C 0) ^^ i) \<bottom>)"
      by auto
    also have "\<dots> = (\<Squnion>n\<in>{1..}. ?L n)" unfolding tt by simp
    also have "\<dots> = (\<Squnion>n\<in>{x. 0 < x}. ?L n)" unfolding ttt by auto
    also have "\<dots> = (\<lambda>s. 1 + (if b s then ert (compile C) 0 s * suminf (\<lambda>i. ?I s ^ i)
                                                  + suminf (\<lambda>i. ?I s ^ i)
                                        else 0))" (is "(\<Squnion>n\<in>{x. 0 < x}. ?f n) = _")
    proof -
      (* pull the limit inwards *)
      let ?W = "wp (compile C) (lift2 b)"
      let ?if = "(\<lambda>n s. 1 + ert (compile C) 0 s * sum ((^) (?W s)) {0..<n} + sum ((^) (?W s)) {0..<n-1})"
      let ?f' = "(%n. (\<lambda>s. (if b s then ?if n s else 1)))"
      have 1: "\<And>n. ?f n = ?f' n"
        by auto
      have 2: "(\<Squnion>n\<in>{x. 0 < x}. ?f' n) = (\<lambda>s. if b s then (\<Squnion>n\<in>{x. 0 < x}. ?if n s) else 1)"
        apply (rule Sup_If) by auto
      { fix s
        have "(\<Squnion>n\<in>{x. 0 < x}. ?if n s) = (\<Squnion>n\<in>{x. 0 < x}. 1 + (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n -1}))"
          by (simp add: add.assoc)
        also have "\<dots> = 1 + (\<Squnion>n\<in>{x. 0 < x}. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1}))"
          apply(subst ennreal_SUP_add_right) by auto
        finally have "(\<Squnion>n\<in>{x. 0 < x}. ?if n s) = 1 + (\<Squnion>n\<in>{x. 0 < x}. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1}))" .
      } note 3=this
      { fix s 
        {
          fix f :: "nat \<Rightarrow> ennreal"      
          have "f ` {x. 0 < x} = (f o Suc) ` UNIV"
            apply(rule) apply (auto simp: image_iff) by (metis Suc_pred') 
        } note k=this

        have t: "(\<lambda>n. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1})) ` {x. 0 < x}
              = (\<lambda>n. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n+1} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n})) `UNIV"
          apply(subst k) by auto              

        have "(\<Squnion>n\<in>{x. 0 < x}. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n - 1}))
              = (\<Squnion>n\<in>UNIV. (ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n+1} + sum ((^) (wp (compile C) (lift2 b) s)) {0..<n}))"
          by(simp only: t)
      } note 4=this

      { fix s
        have n: "\<And>x::nat. {0..<x} = {..<x}" by auto

        have i: "(\<Squnion>n. ert (compile C) 0 s * sum ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) {..<n + 1})
            = ert (compile C) 0 s * (\<Squnion>n. sum ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) {..<n + 1})"
          by (simp only: SUP_mult_left_ennreal)


        have ii: "(\<Squnion>n. sum ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) {..<n + 1})
                = (\<Squnion>n. sum ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) {..<n})"
          apply(rule SUP_shift_mono)   by (auto intro: incseq_SucI)
          
        have " (\<Squnion>n. ert (compile C) 0 s * sum ((^) (wp (compile C) (lift2 b) s)) {0..<n + 1} +
                    sum ((^) (wp (compile C) (lift2 b) s)) {0..<n})
            =  (ert (compile C) 0 s * suminf ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)) +
         suminf ((^) (wp (compile C) (\<lambda>s. if b s then 1 else 0) s)))"
          apply(subst ennreal_SUP_add)
            subgoal by(auto simp: incseq_SucI intro: incseqmult)
            subgoal by(auto simp: n incseq_sumI)
            by(simp only: i suminf_eq_SUP lift2_def n ii)
      } note 5=this
      show ?thesis unfolding 1 2 3 4 5 by auto
    qed
    also have "\<dots> = (%s. 1 + (if b s then (1 + ert (compile C) 0 s) / (1- ?I s) else 0))"
      apply(rule ext)
      subgoal for s
      proof (cases "b s")
        case True
        note b=this
        have kk: "(\<lambda>s. if \<not> b s then f s else 0) = (\<lambda>s. if b s then 0 else  f s)" by auto
        term ?I
        show ?thesis
        proof (cases "?I s < 1") 
          case True
          have geom_series: "(\<Sum>n. (?I s) ^ n) = 1 / (1 - ?I s)" using True 
            by (rule suminf_geometric_ennreal)
          show ?thesis unfolding geom_series using True
            apply (simp add: ennreal_times_divide)
            by (metis (no_types, lifting) add.commute comm_semiring_class.distrib ennreal_times_divide mult.right_neutral) 
        next
          case False
          with wp_le1 have 1: "?I s = 1" 
            by (metis (mono_tags, lifting) eq_refl linorder_cases not_le zero_le_one)  
          show ?thesis by(simp add: 1 b sum1)
        qed
      next
        case False then show ?thesis by auto
      qed
      done
    finally show ?thesis unfolding k(2) by auto 
  qed

  let ?I = "(wp (compile C) (\<lambda>s. if b s then 1 else 0))"
  let ?F = "wp (compile C) (\<lambda>s. if b s then 0 else f s)"

  { fix s
    have "(1 + ert (compile C) 0 s) / (1- ?I s) + ?F s / (1 - ?I s)
      = (1 + ert (compile C) 0 s + ?F s) / (1 - ?I s)"
    proof (cases "?I s < 1")
      case True
      then show ?thesis using hauptnenner by blast
    next
      case False
      with wp_le1 have "?I s = 1" 
          by (metis (mono_tags, lifting) eq_refl linorder_cases not_le zero_le_one)    
      then show ?thesis by auto
    qed
  } note l=this

  have "?E f = ?E 0 + wp (compile (While b C)) f" by(rule decompose_ert)
  also have "\<dots> = ?R 0 
              + (\<lambda>s. if b s then wp (compile C) (\<lambda>s. if b s then 0 else f s) s / (1 - wp (compile C) (\<lambda>s. if b s then 1 else 0) s) else f s)"
    by(simp only: 1 thm3[OF assms(1)]) 
  also 
    have "\<dots> = (%s. 1 + (if b s then (1 + ert (compile C) 0 s) / (1- ?I s)
                                           + ?F s / (1 - ?I s)
                                                      else f s))" unfolding k(2) by auto
  also have "\<dots> = (%s. 1 + (if b s then (1 + ert (compile C) 0 s + ?F s) / (1 - ?I s)
                                                      else f s))"
    by (auto simp add: l)
  also have "\<dots> = ?R f" apply(rule ext) apply simp
    using decompose_ert by (metis (no_types, lifting) add.assoc plus_fun_apply)
  finally show ?thesis .
qed
 


end