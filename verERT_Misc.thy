\<^marker>\<open>creator "Johannes Hölzl"\<close>
theory verERT_Misc
  imports "Markov_Models.Markov_Models" "~~/src/HOL/Library/Function_Algebras"
begin

lemma sup_continuous_apply2[order_continuous_intros]: "sup_continuous (\<lambda>f. f x y)"
  using sup_continuous_apply sup_continuous_applyD by fastforce

lemma measurable_ident_subsets:
  "space M = space M' \<Longrightarrow> sets M' \<subseteq> sets M \<Longrightarrow> (\<lambda>x. x) \<in> measurable M M'"
  by (metis measurable_id measurable_iff_sets subset_trans)

lemma sets_stream_space_mono:
  "space N = space M \<Longrightarrow> M \<subseteq> N \<Longrightarrow> sets (stream_space M) \<subseteq> sets (stream_space N)"
  apply (rule sets_stream_space_in_sets)
  apply (simp add: space_stream_space)
  apply (rule measurable_compose[OF _ measurable_ident_subsets[of N]])
  apply auto
  done

lemma measurable_case_stream[measurable (raw)]:
  "(\<lambda>\<omega>. f (shd \<omega>) (stl \<omega>)) \<in> measurable M N \<Longrightarrow> (\<lambda>(x##\<omega>) \<Rightarrow> f x \<omega>) \<in> measurable M N"
  unfolding stream.case_eq_if .

lemma measurable_cong_restrictI:
  "(\<And>x. x \<in> space (restrict_space M X) \<Longrightarrow> f x = f' x) \<Longrightarrow> f' \<in> M \<rightarrow>\<^sub>M N \<Longrightarrow> f \<in> measurable (restrict_space M X) N"
  apply (subst measurable_cong)
  apply (simp add: space_restrict_space)
  apply (rule measurable_restrict_space1)
  apply assumption
  done

lemma countable_lfp: \<comment> \<open>from lochbihler2016esop\<close>
  assumes step: "\<And>Y. countable Y \<Longrightarrow> countable (F Y)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F)"
by(subst sup_continuous_lfp[OF cont])(simp add: countable_funpow[OF step])

lemma lfp_Collect: assumes F: "mono F" shows "{x. lfp F x} = lfp (\<lambda>X. {x. F (\<lambda>x. x \<in> X) x})"
proof (subst lfp_rolling[of Collect, symmetric]; clarsimp simp: mono_def)
  show "X \<subseteq> Y \<Longrightarrow> F (\<lambda>x. x \<in> X) x \<Longrightarrow> F (\<lambda>x. x \<in> Y) x" for X Y x
    using monoD[OF F, of "\<lambda>x. x \<in> X" "\<lambda>x. x \<in> Y"] by (auto simp: le_fun_def)
qed auto

lemma countable_lfp_apply:
  assumes step: "\<And>Y x. (\<And>x. countable (Y x)) \<Longrightarrow> countable (F Y x)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F x)"
proof -
  { fix n
    have "\<And>x. countable ((F ^^ n) bot x)"
      by(induct n)(auto intro: step) }
  thus ?thesis using cont by(simp add: sup_continuous_lfp)
qed

lemma nn_integral_enat':
  fixes f :: "'a \<Rightarrow> enat"
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M count_space UNIV"
  shows "(\<integral>\<^sup>+x. ennreal_of_enat (f x) \<partial>M) =
    \<infinity> * emeasure M {\<omega>\<in>space M. f \<omega> = \<infinity>} + (\<Sum>i. i * emeasure M {\<omega>\<in>space M. f \<omega> = i})"
proof -
  have "(\<integral>\<^sup>+x. ennreal_of_enat (f x) \<partial>M) =
    (\<integral>\<^sup>+x. \<infinity> * indicator {\<omega>\<in>space M. f \<omega> = \<infinity>} x + (\<Sum>i. of_nat i * indicator {\<omega>\<in>space M. f \<omega> = i} x) \<partial>M)"
    apply (intro nn_integral_cong)
    subgoal for x
      by (auto split: split_indicator intro!: suminf_cmult_indicator[symmetric] simp: disjoint_family_on_def)
    done
  also have "\<dots> = \<infinity> * emeasure M {\<omega>\<in>space M. f \<omega> = \<infinity>} + (\<Sum>i. of_nat i * emeasure M {\<omega>\<in>space M. f \<omega> = i})"
    by (simp add: nn_integral_cmult_indicator nn_integral_add nn_integral_suminf suminf_0_le
             del: ereal_infty_mult)+
  finally show ?thesis .
qed

lemma (in sigma_finite_measure) nn_integral_enat: \<comment> \<open>requirement of sigma-finite measures could be removed\<close>
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M count_space UNIV"
  shows "(\<integral>\<^sup>+x. ennreal_of_enat (f x) \<partial>M) = (\<integral>\<^sup>+x. ennreal_of_enat x * emeasure M {\<omega>\<in>space M. f \<omega> = x} \<partial>count_space UNIV)"
proof -
  interpret sigma_finite_measure "count_space (UNIV::enat set)"
    by (rule sigma_finite_measure_count_space)
  interpret EM: pair_sigma_finite "count_space (UNIV::enat set)" M
    proof qed

  have "(\<integral>\<^sup>+x. ennreal_of_enat (f x) \<partial>M) =
    (\<integral>\<^sup>+x. \<integral>\<^sup>+n. ennreal_of_enat n * indicator {\<omega>\<in>space M. f \<omega> = n} x \<partial>count_space UNIV \<partial>M)"
    apply (intro nn_integral_cong)
    subgoal for x
      by (subst nn_integral_count_space'[where A="{f x}"]) auto
    done
  also have "\<dots> = (\<integral>\<^sup>+n. \<integral>\<^sup>+x. ennreal_of_enat n * indicator {\<omega>\<in>space M. f \<omega> = n} x \<partial>M \<partial>count_space UNIV)"
    apply (rule EM.Fubini') (* apply auto *) sorry
  also have "\<dots> = (\<integral>\<^sup>+n. ennreal_of_enat n * emeasure M {\<omega>\<in>space M. f \<omega> = n} \<partial>count_space UNIV)"
    by (intro nn_integral_cong nn_integral_cmult_indicator) auto
  finally show ?thesis .
qed

lemma sfirst_eq_infty: "alw (not P) \<omega> \<Longrightarrow> sfirst P \<omega> = \<infinity>"
  by (metis (full_types) enat_ord_simps(4) not_alw_not sfirst_finite)

lemma sup_continuous_sfirstF: "sup_continuous (\<lambda>F \<omega>. if P \<omega> then 0 else eSuc (F (stl \<omega>)))"
  by (intro order_continuous_intros sup_continuous_eSuc)

lemma sfirst_eq_lfp:
  fixes P :: "'a stream \<Rightarrow> bool"
  defines "F \<equiv> \<lambda>F \<omega>. if P \<omega> then 0 else eSuc (F (stl \<omega>))"
  shows "sfirst P \<omega> = lfp F \<omega>"
proof -
  have "mono F"
    by (auto simp: F_def mono_def le_fun_def)
  have F: "lfp F = (\<lambda>\<omega>. if P \<omega> then 0 else eSuc ((lfp F) (stl \<omega>)))"
    by (subst lfp_unfold[OF \<open>mono F\<close>]) (auto simp: F_def)

  show ?thesis
  proof cases
    assume "ev P \<omega>"
    then show "sfirst P \<omega> = lfp F \<omega>"
    proof (induction rule: ev_induct_strong)
      case (base \<omega>) then show ?case
        by (subst F) auto
    next
      case (step \<omega>) then show ?case
        by (subst F) auto
    qed
  next
    assume "\<not> ev P \<omega>"
    then have "alw (not P) \<omega>"
      unfolding not_ev_iff .
    moreover then have "enat i \<le> lfp F \<omega>" for i
    proof (induction i arbitrary: \<omega>)
      case 0 then show ?case
        by (simp add: enat_0)
    next
      case (Suc i) from Suc.IH[of "stl \<omega>"] Suc.prems show ?case
        by (subst F) (auto simp: eSuc_enat[symmetric])
    qed
    then have "lfp F \<omega> = \<infinity>"
      by (metis eSuc_eq_infinity_iff enat_the_enat iless_Suc_eq less_irrefl)
    ultimately show ?thesis
      by (simp add: sfirst_eq_infty)
  qed
qed

lemma sfirst_translate:
  "inj f \<Longrightarrow> sfirst P (smap f \<omega>) = sfirst (\<lambda>x. P (smap f x)) \<omega>"
  unfolding sfirst_eq_lfp
  by (rule lfp_transfer[where \<alpha>="\<lambda>F \<omega>. F (smap f \<omega>)", unfolded fun_eq_iff, rule_format])
     (auto intro!: order_continuous_intros sup_continuous_eSuc sup_continuous_mono simp: le_fun_def)

lemma sup_continuous_ennreal_of_enat[order_continuous_intros]:
  "sup_continuous f \<Longrightarrow> sup_continuous (\<lambda>i. ennreal_of_enat (f i))"
  by (rule sup_continuous_compose[of ennreal_of_enat])
     (auto simp: sup_continuous_def ennreal_of_enat_Sup SUP_image)

lemma (in MC_syntax) sfirst_lfp:
  "(\<integral>\<^sup>+\<omega>. sfirst (HLD Y) \<omega> \<partial>T x) = lfp (\<lambda>F x. \<integral>\<^sup>+y. (F y + 1) * indicator (-Y) y \<partial>K x) x"
  unfolding sfirst_eq_lfp
  apply (subst lfp_transfer[where \<alpha>="\<lambda>F \<omega>. ennreal_of_enat (F \<omega>)" and g="\<lambda>F \<omega>. if HLD Y \<omega> then 0 else F (stl \<omega>) + 1"])
  apply (auto simp: bot_enat_def le_fun_def fun_eq_iff add.commute sup_absorb1
              simp del: sup_ereal_def
              intro!: order_continuous_intros sup_continuous_mono sup_continuous_eSuc)
  apply (rule nn_integral_lfp[where N=S])
  apply (auto simp del: sup_ereal_def split: split_indicator
              intro!: order_continuous_intros sup_continuous_eSuc)
  apply (subst nn_integral_T)
  apply simp
  apply (rule nn_integral_cong)
  apply (auto simp: nn_integral_add cong del: nn_integral_cong split: split_indicator)
  done

lemma borel_measurable_ennreal_of_enat[measurable]: "ennreal_of_enat \<in> count_space UNIV \<rightarrow>\<^sub>M borel"
  by (rule measurable_compose_countable'[where g=ennreal_of_enat and f="\<lambda>i x. i" and I="ennreal_of_enat ` UNIV"])
     auto

lemma measurable_funpow [measurable]:
  assumes [measurable]: "\<And>f. f \<in> M \<rightarrow>\<^sub>M N \<Longrightarrow> F f \<in> M \<rightarrow>\<^sub>M N"
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M N"
  shows "(F ^^ n) f \<in> M \<rightarrow>\<^sub>M N"
  by (induction n) auto

lemma integral_map_pmf:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "(LINT x | map_pmf f M. g x) = (LINT x | M. g (f x))"
  unfolding map_pmf_rep_eq by (subst integral_distr) auto

lemma sfirst_eq_enatD: "sfirst P \<omega> = enat n \<Longrightarrow> P (sdrop n \<omega>)"
  apply (induction n arbitrary: \<omega>)
  apply (auto simp: enat_0 eSuc_enat[symmetric] sfirst_eq_0)
  subgoal for n \<omega>
    by (cases \<omega>) (simp add: sfirst_Stream split: if_split_asm)
  done

lemma sfirst_eq_eSuc: "sfirst P \<omega> = eSuc n \<longleftrightarrow> (\<not> P \<omega> \<and> sfirst P (stl \<omega>) = n)"
  by (cases \<omega>) (simp add: sfirst_Stream)

lemma eSuc_le_sfirst_iff: "eSuc n \<le> sfirst P \<omega>  \<longleftrightarrow> (\<not> P \<omega> \<and> n \<le> sfirst P (stl \<omega>))"
  by (cases \<omega>) (simp add: sfirst_Stream)

end
