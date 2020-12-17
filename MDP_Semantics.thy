\<^marker>\<open>creator "Johannes Hölzl"\<close>
chapter \<open>MDP Semantics for PGCL\<close>
theory MDP_Semantics
  imports PGCL
begin

paragraph \<open>Summary\<close>

text \<open>This theory provides an operational interpretation of pGCL running times as MDPs,
      and proves its equivalence to pGCL's the denotational expectation running
         transformer semantics.\<close>

paragraph \<open>Main Lemmas\<close>

text \<open>
  \<^item> ert_eq_Ert: the equivalence of pGCL's the denotational expectation running
         transformer semantics and an operational interpretation of pGCL running times as MDPs.\<close>

section \<open>Operational Semantics of pGCL\<close>


abbreviation det :: "'s pgcl \<Rightarrow> 's \<Rightarrow> ('s pgcl \<times> 's) pmf set" ("\<lless> _, _ \<ggreater>") where
  "det c s \<equiv> {return_pmf (c, s)}"

fun K :: "('a pgcl \<times> 'a) \<Rightarrow> ('a pgcl \<times> 'a) pmf set"
where
  "K (Empty, s) = \<lless>Empty, s\<ggreater>"
| "K (Skip, s) = \<lless>Empty, s\<ggreater>"
| "K (Halt, s) = \<lless>Halt, s\<ggreater>"
| "K (Assign u, s) = map_pmf (\<lambda>s'. (Empty, s')) ` {u s}"
| "K (Seq c\<^sub>1 c\<^sub>2, s) = map_pmf (apfst (\<lambda>Empty \<Rightarrow> c\<^sub>2 | Halt \<Rightarrow> Halt | c' \<Rightarrow> Seq c' c\<^sub>2)) ` K (c\<^sub>1, s)"
| "K (Par c\<^sub>1 c\<^sub>2, s) = \<lless>c\<^sub>1, s\<ggreater> \<union> \<lless>c\<^sub>2, s\<ggreater>"
| "K (If g c\<^sub>1 c\<^sub>2, s) = (if g s then \<lless>c\<^sub>1, s\<ggreater> else \<lless>c\<^sub>2, s\<ggreater>)"
| "K (While g c, s) = (if g s then \<lless>Seq c (While g c), s\<ggreater> else \<lless>Empty, s\<ggreater>)"

interpretation Markov_Decision_Process K
proof
  show "K s \<noteq> {}" for s :: "'a pgcl \<times> 'a"
    by (induction s rule: K.induct) auto
qed

abbreviation Estep :: "('a pgcl \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> 'a pgcl \<Rightarrow> 'a \<Rightarrow> ennreal"
where
  "Estep F c s \<equiv> (\<Squnion>D\<in>K (c, s). \<integral>\<^sup>+(c', s'). F c' s' \<partial>measure_pmf D)"

context
  fixes f :: "'a \<Rightarrow> ennreal"
begin

primrec cost :: "'a pgcl \<Rightarrow> 'a \<Rightarrow> ennreal \<Rightarrow> ennreal"
where
  "cost Empty       s _ = f s"
| "cost Skip        _ x = 1 + x"
| "cost Halt        _ _ = 0"
| "cost (Assign _)  _ x = 1 + x"
| "cost (Seq c1 _)  s x = (if c1 = Empty then x else cost c1 s x)"
| "cost (Par _ _ )  s x = x"
| "cost (If _ _ _)  _ x = 1 + x"
| "cost (While g c) _ x = 1 + x"

lemma sup_continuous_cost[order_continuous_intros]: "sup_continuous (cost c s)"
  by (induction c arbitrary: s)
     (auto intro: order_continuous_intros simp: cost.simps[abs_def])

\<comment> \<open>The following measurability proof is very ugly it should be much simpler...\<close>
declare [[inductive_internals]]
inductive_set rF_ranges where
  "{Empty} \<in> rF_ranges "
| "{Skip} \<in> rF_ranges"
| "{Halt} \<in> rF_ranges"
| "{Assign f | f. True} \<in> rF_ranges"
| "X \<in> rF_ranges \<Longrightarrow> {Seq c1 c2 | c1 c2. c1 \<in> X} \<in> rF_ranges"
| "{Par c1 c2 | c1 c2. True} \<in> rF_ranges"
| "{If g c1 c2 | g c1 c2. True} \<in> rF_ranges "
| "{While g c | g c. True} \<in> rF_ranges "

lemma empty_in_rF_ranges: "X \<in> rF_ranges \<Longrightarrow> Empty \<in> X \<longleftrightarrow> X = {Empty}"
  by (induction rule: rF_ranges.induct) auto

lemma cover_rF_ranges: "c \<in> \<Union>rF_ranges"
  by (induction c) (insert rF_ranges.intros, blast+)

lemma countable_rF_ranges: "countable rF_ranges"
  unfolding rF_ranges_def rF_rangesp_def lfp_Collect[OF rF_rangesp.mono]
  apply (intro countable_lfp)
  unfolding Collect_disj_eq singleton_conv Setcompr_eq_image
  apply auto []
  apply (intro sup_continuous_sup sup_continuous_const, auto simp: sup_continuous_def)
  done

lemma measurable_cost':
  "(\<lambda>x. cost (fst x) (fst (snd x)) (snd (snd x))) \<in> (count_space UNIV \<Otimes>\<^sub>M count_space UNIV \<Otimes>\<^sub>M borel) \<rightarrow>\<^sub>M borel"
  (is "?p cost \<in> ?M \<rightarrow>\<^sub>M borel")
proof (rule measurable_piecewise_restrict[of "vimage fst ` rF_ranges"]; clarsimp?)
  show "countable (vimage fst ` rF_ranges)"
    by (intro countable_image countable_rF_ranges)
  show "\<exists>x\<in>rF_ranges. \<omega> \<in> x" for \<omega> :: "'a pgcl"
    using cover_rF_ranges by auto

  let ?P = "\<lambda>X. restrict_space ?M (vimage fst X)"
  have *: "(\<And>c s x. c \<in> X \<Longrightarrow> cost c s x = f' c s x) \<Longrightarrow> ?p f' \<in> ?M \<rightarrow>\<^sub>M borel \<Longrightarrow> ?p cost \<in> ?P X \<rightarrow>\<^sub>M borel" for f' X
    apply (subst measurable_cong[where g="?p f'"])
    apply (simp add: space_restrict_space)
    apply (rule measurable_restrict_space1)
    apply assumption
    done

  show "?p cost \<in> ?P X \<rightarrow>\<^sub>M borel" if "X \<in> rF_ranges" for X
    using that
  proof induction
    case 1 then show ?case
      by (rule *[of _ "\<lambda>c s x. f s"]) (auto intro: measurable_compose)
  next
    case 3 then show ?case
      by (rule *[of _ "\<lambda>\<omega>. 0"]) auto
  next
    case (5 X)
    show ?case
    proof cases
      assume "Empty \<in> X"
      then have [simp]: "X = {Empty}"
        by (simp add: empty_in_rF_ranges 5)
      show ?case
        by (rule *[of _ "\<lambda>c s x. x"]) auto
    next
      assume X: "Empty \<notin> X"
      show ?thesis
      proof (rule measurable_cong[THEN iffD2, OF _ measurable_compose[OF _ "5.IH"]])
        show "(\<lambda>x. (left (fst x), snd x)) \<in> ?P {Seq c1 c2 |c1 c2. c1 \<in> X} \<rightarrow>\<^sub>M ?P X"
          by (intro measurable_restrict_space2)
             (auto simp: space_restrict_space intro: measurable_compose intro!: measurable_Pair measurable_restrict_space1)
      qed (auto simp: space_restrict_space X)
    qed
  next
    case 6 then show ?case
      by (rule *[of _ "\<lambda>c s x. x"]) auto
  qed (rule *[of _ "\<lambda>c s x. 1 + x"]; auto)+
qed

lemma measurable_cost[measurable (raw)]:
  "g \<in> M \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow> h \<in> M \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow> j \<in> M \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>x. cost (g x) (h x) (j x)) \<in> M \<rightarrow>\<^sub>M borel"
  using measurable_compose[OF _ measurable_cost', of "\<lambda>x. (g x, h x, j x)" M] by simp

lemma sup_continuous_cost_stream: "sup_continuous (\<lambda>F. \<lambda>((c, s)##\<omega>) \<Rightarrow> cost c s (F \<omega>))"
  unfolding stream.case_eq_if[abs_def] prod.case_eq_if
  by (intro order_continuous_intros sup_continuous_cost[THEN sup_continuous_compose])

lemma measurable_cost_stream[measurable]:
  "F \<in> St \<rightarrow>\<^sub>M borel \<Longrightarrow> (\<lambda>((c, s)##\<omega>) \<Rightarrow> cost c s (F \<omega>)) \<in> St \<rightarrow>\<^sub>M borel"
  apply measurable
  apply (rule measurable_ident_subsets[where M'="stream_space (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"])
  apply (simp add: space_stream_space space_pair_measure)
  apply (intro sets_stream_space_mono)
  apply (auto simp: space_pair_measure intro: measurable_compose[OF measurable_shd])
  done

definition r :: "('a pgcl \<times> 'a) stream \<Rightarrow> ennreal"
where
  "r = lfp (\<lambda>F. \<lambda>((c, s)##\<omega>) \<Rightarrow> cost c s (F \<omega>))"

lemma r_Stream: "r ((c, s) ## \<omega>) = cost c s (r \<omega>)"
  unfolding r_def by (subst lfp_unfold[OF sup_continuous_mono[OF sup_continuous_cost_stream]]) auto

lemma measurable_r[measurable]: "r \<in> St \<rightarrow>\<^sub>M borel"
  unfolding r_def by (rule borel_measurable_lfp[OF sup_continuous_cost_stream]) measurable

definition cost_step :: "('a pgcl \<Rightarrow> 'a \<Rightarrow> ennreal) \<Rightarrow> ('a pgcl \<Rightarrow> 'a \<Rightarrow> ennreal)"
where
  "cost_step F c s = cost c s (Estep F c s)"

lemma cost_step_alt: "cost_step F c s = Estep (\<lambda>c' s'. cost c s (F c' s')) c s"
  by (induction c arbitrary: s F) (auto simp: split_beta' cost_step_def nn_integral_add SUP_image)

lemma cost_step_Empty[simp]: "cost_step F Empty s = f s"
  by (simp add: cost_step_def)

lemma cost_step_Halt[simp]: "cost_step F Halt s = 0"
  by (simp add: cost_step_def)

lemma cost_step_Seq: "cost_step F (Seq c d) s =
    (if c = Empty then F d s else cost_step (\<lambda>c. F (case c of Empty \<Rightarrow> d | Halt \<Rightarrow> Halt | _ \<Rightarrow> Seq c d)) c s)"
  by (auto simp add: split_beta' cost_step_def SUP_image
           intro!: arg_cong[where f="cost _ _"] SUP_cong nn_integral_cong arg_cong[where f="\<lambda>x. F x _"]
           split: pgcl.split)

lemma cost_step_While[simp]: "cost_step F (While g c) s = 1 + F (if g s then Seq c (While g c) else Empty) s"
  by (simp add: cost_step_def)

lemma sup_continuous_cost_step: "sup_continuous cost_step"
  unfolding cost_step_def[abs_def]
  by (auto simp: prod.case_eq_if intro!: order_continuous_intros sup_continuous_compose[OF sup_continuous_cost])

end

lemma cost_mono: "(d = Empty \<Longrightarrow> f s \<le> g s) \<Longrightarrow> (d \<noteq> Empty \<Longrightarrow> d \<noteq> Halt \<Longrightarrow> F \<le> G) \<Longrightarrow> cost f d s F \<le> cost g d s G"
  by (induction d) auto

lemma cost_step_mono: "(c = Empty \<Longrightarrow> f s \<le> g s) \<Longrightarrow>
  (\<And>D c' s'. c \<noteq> Halt \<Longrightarrow> c \<noteq> Empty \<Longrightarrow> D \<in> K (c, s) \<Longrightarrow> (c', s') \<in> D \<Longrightarrow> F c' s' \<le> G c' s') \<Longrightarrow>
  cost_step f F c s \<le> cost_step g G c s"
  by (auto simp: cost_step_def intro!: cost_mono SUP_subset_mono nn_integral_mono_AE AE_pmfI)

abbreviation Ert :: "('a \<Rightarrow> ennreal) \<Rightarrow> 'a pgcl \<Rightarrow> ('a \<Rightarrow> ennreal)"
where
  "Ert f c s \<equiv> E_sup (c, s) (\<lambda>\<omega>. r f ((c, s) ## \<omega>))"

lemma mono_Ert: "mono Ert"
  unfolding r_def
  by (intro monoI le_funI E_sup_mono lfp_mono[THEN le_funD])
     (auto intro!: cost_mono split: stream.split dest: le_funD)

lemma Ert_Stream: "Ert f c s = cost_step f (\<lambda>c' s'. E_sup (c', s') (\<lambda>\<omega>. r f ((c', s') ## \<omega>))) c s"
proof -
  have *: "F \<in> St \<rightarrow>\<^sub>M borel \<Longrightarrow> E_sup x (\<lambda>\<omega>. cost f c s (F \<omega>)) = cost f c s (E_sup x F)"
    for F and x :: "'a pgcl \<times> 'a"
    by (induction c arbitrary: x F) (auto simp: E_sup_add_right E_sup_const)
  show ?thesis
    by (subst E_sup_iterate)
       (auto intro!: SUP_cong nn_integral_cong_AE AE_pmfI simp: cost_step_alt r_Stream[of f c] *)
qed

lemma Ert_eq_abs: "Ert f = lfp (cost_step f)"
  unfolding r_def
proof (rule lfp_transfer_bounded[where \<alpha>="\<lambda>F. (\<lambda>c s. E_sup (c, s) (\<lambda>\<omega>. F ((c, s) ## \<omega>)))"])
  fix F :: "('a pgcl \<times> 'a) stream \<Rightarrow> ennreal" assume F[measurable]: "F \<in> St \<rightarrow>\<^sub>M borel"
  have *: "E_sup x (\<lambda>\<omega>. cost f c s (F (x ## \<omega>))) = cost f c s (E_sup x (\<lambda>\<omega>. F (x ## \<omega>)))"
    for c s x by (induction c arbitrary: s x) (simp_all add: E_sup_add_right E_sup_const)
  show "(\<lambda>c s. E_sup (c, s) (\<lambda>\<omega>. case (c, s) ## \<omega> of (c, s) ## \<omega> \<Rightarrow> cost f c s (F \<omega>))) =
    cost_step f (\<lambda>c s. E_sup (c, s) (\<lambda>\<omega>. F ((c, s) ## \<omega>)))"
    by (subst E_sup_iterate)
       (auto intro!: SUP_cong nn_integral_cong_AE AE_pmfI * simp: cost_step_alt[abs_def])
next
  show "(\<lambda>c s. E_sup (c::'a pgcl, s) (\<lambda>\<omega>. (\<Squnion>i. C i) ((c, s) ## \<omega>))) =
      (\<Squnion>i. (\<lambda>c s. E_sup (c, s) (\<lambda>\<omega>. C i ((c, s) ## \<omega>))))"
    if C: "incseq C" and [measurable]: "\<And>i. C i \<in> St \<rightarrow>\<^sub>M borel" for C
    by (simp add: fun_eq_iff mono_compose[OF C] E_sup_SUP SUP_image)
qed (auto intro: sup_continuous_cost_step sup_continuous_cost_stream simp: SUP_apply[abs_def] le_fun_def E_sup_const)

lemma Ert_eq: "Ert f c s = lfp (cost_step f) c s"
  using Ert_eq_abs[of f] by (auto simp: fun_eq_iff)

lemma Ert_induct[consumes 1, case_names step]:
  assumes "P c s y"
  assumes *:
    "\<And>F c s y. P c s y \<Longrightarrow> (\<And>c s y. P c s y \<Longrightarrow> F c s \<le> y) \<Longrightarrow> (\<And>c s. F c s \<le> Ert f c s) \<Longrightarrow>
      cost_step f F c s \<le> y"
  shows "Ert f c s \<le> y"
  using `P c s y`
  unfolding Ert_eq
proof (induction arbitrary: s c y rule: lfp_ordinal_induct[OF sup_continuous_mono[OF sup_continuous_cost_step[where f=f]]])
  have **: "lfp (cost_step f) = Ert f"
    by (intro ext Ert_eq[symmetric])
  case (1 F) then show ?case
    unfolding ** cost_step_def[symmetric] by (intro *) (auto simp: le_fun_def)
qed (auto intro: SUP_least)

lemma Ert_Empty[simp]: "Ert f Empty s = f s"
  by (simp add: r_Stream E_sup_const)

lemma Ert_Halt[simp]: "Ert f Halt s = 0"
  by (simp add: r_Stream E_sup_const)

lemma Ert_Seq: "Ert f (Seq a b) s = Ert (Ert f b) a s"
proof (rule antisym)
  show "Ert f (Seq a b) s \<le> Ert (Ert f b) a s"
  proof (coinduction arbitrary: a s rule: Ert_induct)
    case (step F a s) with step(2)[of Halt] show ?case
      by (rewrite in "_ \<le> \<hole>"  Ert_Stream)
         (auto simp add: cost_step_Seq intro!: cost_step_mono split: pgcl.split)
  qed
  show "Ert (Ert f b) a s \<le> Ert f (Seq a b) s"
  proof (coinduction arbitrary: a s rule: Ert_induct)
    case (step F a s) with step(2)[of Empty] step(2)[of Halt] show ?case
      by (rewrite in "_ \<le> \<hole>"  Ert_Stream)
         (auto simp add: cost_step_Seq intro!: cost_step_mono split: pgcl.split)
   qed
qed

lemma Ert_While: "Ert f (While g c) s = lfp (\<lambda>F s. 1 + (if g s then Ert F c s else f s)) s"
proof (rule antisym)
  let ?f = "\<lambda>F s. 1 + (if g s then F c s else f s)"
  have single: "Ert f (While g c) s = ?f (Ert (Ert f (While g c))) s" for s
    by (rewrite Ert_Stream) (simp add: Ert_Seq)
  then have "lfp (\<lambda>F. ?f (Ert F)) \<le> Ert f (While g c)"
    by (intro lfp_lowerbound) simp
  then show "lfp (\<lambda>F. ?f (Ert F)) s \<le> Ert f (While g c) s"
    by (simp add: le_fun_def)

  have w: "mono (\<lambda>F. cost_step (?f F) F)"
    by (auto simp: mono_def le_fun_def intro!: cost_step_mono)

  let ?w = "lfp (\<lambda>F. cost_step (?f F) F)"
  have w_unfold: "?w d s = cost_step (?f ?w) ?w d s" for d s
    by (subst lfp_unfold[OF w]) simp

  have [simp]: "?w Empty s = ?f ?w s" for s
    by (subst w_unfold) simp

  have [simp]: "?w Halt s = 0" for s
    by (subst w_unfold) simp

  define d where "d = c"
  define t where "t = Seq d (While g c)"
  then have "(t = While g c \<and> d = c \<and> g s) \<or> t = Seq d (While g c)"
    by auto
  then have "Ert f t s \<le> (if t = While g c then 1 else 0) + ?w d s"
  proof (coinduction arbitrary: t d s rule: Ert_induct)
    case (step F t d s)
    have [simp]: "\<not> g s \<Longrightarrow> F (While g c) s \<le> 1 + f s" "g s \<Longrightarrow> F (While g c) s \<le> 1 + ?w c s" for s
      using step(3)[of "While g c" s] by (auto simp: single intro: step)
    have "F (case d of Empty \<Rightarrow> While g c | Halt \<Rightarrow> Halt | _ \<Rightarrow> Seq d (While g c)) s \<le> ?w d s" for d s
      using step(3)[of Halt s] by (auto intro: step split: pgcl.split)
    with step(1) show ?case
      by safe (auto intro!: cost_step_mono simp: step cost_step_Seq w_unfold[of d s])
  qed
  also have "?w = lfp (\<lambda>F. Ert (?f F))"
    unfolding Ert_eq by (rule lfp_lfp[symmetric]) (auto intro!: cost_step_mono simp: le_fun_def)
  finally have "Ert f (While g c) s \<le> 1 + (if g s then \<dots> c s else f s)"
    unfolding t_def d_def by (rewrite Ert_Stream) simp
  also have "\<dots> = lfp (\<lambda>F. ?f (Ert F)) s"
    by (rewrite lfp_rolling[symmetric, of ?f, OF _ mono_Ert]) (auto simp: mono_def le_fun_def)
  finally show "Ert f (While g c) s \<le> \<dots>"
    .
qed

lemma ert_eq_Ert: "ert c f s = Ert f c s"
proof (induction c arbitrary: s f)
  case Skip then show ?case
    by (subst Ert_Stream) (auto simp: cost_step_def)
next
  case (Assign f) then show ?case
    by (subst Ert_Stream) (auto simp: cost_step_def)
next
  case (Par c1 c2) then show ?case
    by (subst Ert_Stream) (auto simp: cost_step_def ac_simps)
next
  case (If g c1 c2) then show ?case
    by (subst Ert_Stream) (auto simp: cost_step_def)
next
  case (Seq c1 c2) then show ?case
    by (simp add: Ert_Seq)
qed (auto simp: Ert_While cong del: if_cong)

end
