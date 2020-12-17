theory Random_Walk
  imports PGCL
begin

lemma add_divide_distrib_ennreal: "(a + b::ennreal) / c = a / c + b / c"
  by (simp add: divide_ennreal_def distrib_right)

lemma e2ennreal_inject: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> e2ennreal x = e2ennreal y \<longleftrightarrow> x = y"
  unfolding e2ennreal_def by (auto simp: max_absorb2 ennreal.e2ennreal'_inject)

lemma e2ennreal_eq_top: "e2ennreal x = top \<longleftrightarrow> x = \<infinity>"
  unfolding top_ennreal_def top_ereal_def
  apply (cases "\<not> 0 \<le> x")
  apply (auto simp add: e2ennreal_neg e2ennreal_infty) []
  apply (rule e2ennreal_inject)
  apply (auto simp: top_ennreal_def)
  done

lemma ennreal_of_enat_add: "ennreal_of_enat (m + n) = ennreal_of_enat m + ennreal_of_enat n"
  by (cases m n rule: enat.exhaust[case_product enat.exhaust]) auto

lemma ennreal_of_enat_eq_top: "ennreal_of_enat e = top \<longleftrightarrow> e = \<infinity>"
  by (cases e) auto

lemma (in MC_syntax) T_translate:
  fixes f
  assumes f: "bij f" and K_f: "\<And>x. K (f x) = map_pmf f (K x)"
  shows "T (f x) = distr (T x) S (smap f)"
proof -
  have f_inv: "f (the_inv f x) = x" and [simp]: "inj f" for x
    using f f_the_inv_into_f[of f UNIV x] by (auto simp: bij_def)
  have K_inv[simp]: "K (the_inv f i) = map_pmf (the_inv f) (K i)" for i
    by (rewrite at "map_pmf _ (K \<hole>)" f_inv[symmetric]) (auto simp: K_f map_pmf_comp the_inv_f_f)

  have "T = (\<lambda>i. distr (T (the_inv f i)) S (smap f))"
  proof (rule T_bisim)
    fix i
    show "prob_space (distr (T (the_inv f i)) S (smap f))"
      by (intro T.prob_space_distr) simp
    show "sets (distr (T (the_inv f i)) S (smap f)) = sets S"
      by simp
    have *: "subprob_space (distr (T x) (stream_space (count_space UNIV)) ((##) x))" for x
      by (intro prob_space_imp_subprob_space T.prob_space_distr) auto

    show "distr (T (the_inv f i)) S (smap f) = measure_pmf (K i) \<bind> (\<lambda>s. distr (distr (T (the_inv f s)) S (smap f)) S ((##) s))"
      apply (subst T_eq_bind)
      apply (subst distr_bind[where K=S])
      apply (auto simp: space_subprob_algebra prob_space_imp_subprob_space T.prob_space_distr K_f)
      apply (subst (1 2) distr_distr)
      apply (auto simp: map_pmf_rep_eq)
      apply (subst bind_distr[where K=S])
      apply (auto simp: space_subprob_algebra prob_space_imp_subprob_space T.prob_space_distr
                        comp_def f_inv
                 intro!: bind_measure_pmf_cong)
      done
  qed
  from this[THEN fun_cong, of "f x"] show ?thesis
    by (simp add: the_inv_f_f)
qed

definition srw :: "int \<Rightarrow> int pmf"
where
  "srw i = map_pmf (\<lambda>True \<Rightarrow> i + 1 | False \<Rightarrow> i - 1) (bernoulli_pmf (1/2))"

lemma set_pmf_srw[simp]: "set_pmf (srw i) = {i - 1, i + 1}"
  by (auto simp add: srw_def set_pmf_bernoulli split: bool.splits)

lemma srw_uminus: "srw (- i) = map_pmf uminus (srw i)"
  apply (intro pmf_eqI)
  unfolding ennreal_inj[symmetric, OF pmf_nonneg pmf_nonneg] ennreal_pmf_map srw_def nn_integral_map_pmf
  apply (subst nn_integral_bernoulli_pmf)
  apply (auto split: split_indicator)
  done

lemma srw_add: "srw (i + t) = map_pmf (\<lambda>i. i + t) (srw i)"
  apply (intro pmf_eqI)
  unfolding ennreal_inj[symmetric, OF pmf_nonneg pmf_nonneg] ennreal_pmf_map srw_def nn_integral_map_pmf
  apply (subst nn_integral_bernoulli_pmf)
  apply (auto split: split_indicator)
  done

context
begin

interpretation srw: MC_syntax srw .

lemma srw_T_uminus: "srw.T (- i) = distr (srw.T i) srw.S (smap uminus)"
  by (rule srw.T_translate)
     (auto simp: srw_uminus bij_def image_iff intro!: exI[of _ "- _"])

lemma srw_T_add: "srw.T (i + t) = distr (srw.T i) srw.S (smap (\<lambda>i. i + t))"
  by (rule srw.T_translate)
     (auto simp: srw_add bij_def image_iff intro!: exI[of _ "_ - t"] inj_onI)

abbreviation h :: "int \<Rightarrow> int stream \<Rightarrow> enat"
where
  "h i \<omega> \<equiv> sfirst (HLD {i}) \<omega>"

abbreviation H :: "int \<Rightarrow> int \<Rightarrow> ennreal"
where
  "H i j \<equiv> (\<integral>\<^sup>+\<omega>. h j (i ## \<omega>) \<partial>srw.T i)"

lemma H_uminus: "H (-i) (-j) = H i j"
  apply (subst srw_T_uminus)
  apply (subst nn_integral_distr)
  using sfirst_translate[of uminus "HLD {-j}" "i ## _"]
  apply (auto simp: HLD_iff[abs_def])
  done

lemma H_add: "H (i + t) (j + t) = H i j"
  apply (subst srw_T_add)
  apply (subst nn_integral_distr)
  using sfirst_translate[of "\<lambda>i. i + t" "HLD {j + t}" "i ## _"]
  apply (auto simp: HLD_iff[abs_def] inj_on_def)
  done

lemma H_split:
  assumes "j \<le> k" "k \<le> i"
  shows "H j i = H j k + H k i"
proof cases
  assume ae: "AE \<omega> in srw.T j. h k (j ## \<omega>) \<noteq> \<infinity>"
  have split_hk:
      "emeasure (srw.T j) (space (srw.T j)) = (\<Sum>n. emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j##\<omega>) = n})"
    using ae
    apply (subst suminf_emeasure)
    apply auto []
    apply (auto simp: disjoint_family_on_def) []
    apply (intro emeasure_eq_AE)
    apply (auto elim: eventually_mono)
    done

  let ?I = "\<lambda>n \<omega>. indicator {\<omega> \<in> space srw.S. h k (j ## \<omega>) = enat n} \<omega> :: ennreal"
  have h_stake: "h k (stake (Suc n) \<omega> @- \<omega>') = enat n \<longleftrightarrow> h k \<omega> = enat n"
    for n \<omega> \<omega>'
    by (induction n arbitrary: \<omega> \<omega>')
       (auto simp: enat_0 sfirst_eq_0 HLD_iff sfirst_Stream eSuc_enat[symmetric])
  have *: "indicator {\<omega> \<in> space srw.S. h k (j ## \<omega>) = enat n} (stake n \<omega> @- \<omega>') = ?I n \<omega>" for n \<omega> \<omega>'
    using h_stake[of n "j ## \<omega>" \<omega>'] by (auto split: split_indicator simp: space_stream_space)
  have **: "(\<integral>\<^sup>+ \<omega>'. ennreal_of_enat (h i (k ## \<omega>')) \<partial>srw.T ((j ## \<omega>) !! n)) * ?I n \<omega> =
    (\<integral>\<^sup>+ \<omega>'. ennreal_of_enat (h i (k ## \<omega>')) \<partial>srw.T k) * ?I n \<omega>" for n \<omega>
    by (auto simp: HLD_iff dest!: sfirst_eq_enatD split: split_indicator)

  have "H j k = \<infinity> * emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j ## \<omega>) = \<infinity>} +
    (\<Sum>n. ennreal n * emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j ## \<omega>) = n})"
    by (subst nn_integral_enat') (auto simp: ennreal_of_nat_eq_real_of_nat)
  moreover have "emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j##\<omega>) = \<infinity>} = 0"
    by (rule AE_iff_measurable[THEN iffD1, OF _ _ ae]) auto
  moreover have "(\<Sum>n. H k i * emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j##\<omega>) = n}) = H k i"
    using split_hk by (subst ennreal_suminf_cmult) (auto simp: )
  ultimately have "H j k + H k i =
      (\<Sum>n. (ennreal n + H k i) * emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j##\<omega>) = n})"
    by (simp add: distrib_right suminf_add[symmetric])
  moreover have "(ennreal n + H k i) * emeasure (srw.T j) {\<omega>\<in>space (srw.T j). h k (j##\<omega>) = n} =
    (\<integral>\<^sup>+\<omega>'. (ennreal n + h i (k ## sdrop n \<omega>')) * ?I n \<omega>' \<partial>srw.T j)" for n
    by (subst srw.nn_integral_T_split[where s=j and n=n])
       (simp_all add: * ** nn_integral_multc nn_integral_add distrib_right sdrop_shift nn_integral_cmult)
  moreover have "(\<integral>\<^sup>+\<omega>. (ennreal n + h i (k ## sdrop n \<omega>)) * ?I n \<omega> \<partial>srw.T j) = (\<integral>\<^sup>+\<omega>. h i (j ## \<omega>) * ?I n \<omega> \<partial>srw.T j)" for n
    apply (intro nn_integral_cong_AE)
    using srw.AE_T_enabled
    apply eventually_elim
  proof (intro ennreal_mult_right_cong refl)
    fix \<omega> assume "srw.enabled j \<omega>" "?I n \<omega> \<noteq> 0"
    then have "srw.enabled j \<omega>" "h k (j ## \<omega>) = enat n" by (auto split: split_indicator_asm)
    with assms(1) have "h i (j ## \<omega>) = enat n + h i (k ## sdrop n \<omega>)"
    proof (induction n arbitrary: \<omega> j)
      case (Suc n) then show ?case
      proof cases
        assume "j \<noteq> k" then show ?case
          using Suc.prems \<open>k \<le> i\<close> Suc.IH[of "shd \<omega>" "stl \<omega>"] srw.enabled_iff[of j \<omega>]
          by (auto simp add: sfirst_eq_eSuc eSuc_enat[symmetric] iadd_Suc)
      qed (simp add: enat_0_iff)
    qed (simp add: sfirst_eq_0 enat_0)
    then show "ennreal (real n) + ennreal_of_enat (h i (k ## sdrop n \<omega>)) = ennreal_of_enat (h i (j ## \<omega>))"
      by (simp add: ennreal_of_enat_add ennreal_of_nat_eq_real_of_nat)
  qed
  ultimately have "H j k + H k i = (\<Sum>n. (\<integral>\<^sup>+\<omega>. h i (j ## \<omega>) * ?I n \<omega> \<partial>srw.T j))"
    by simp
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. h i (j ## \<omega>) * (\<Sum>n. ?I n \<omega>) \<partial>srw.T j)"
    by (simp add: nn_integral_suminf ennreal_suminf_cmult[symmetric] del: ennreal_suminf_cmult)
  also have "\<dots> = (\<integral>\<^sup>+\<omega>. h i (j ## \<omega>) \<partial>srw.T j)"
    apply (rule nn_integral_cong_AE)
    using ae
    apply eventually_elim
    apply (auto simp: suminf_indicator disjoint_family_on_def)
    apply (subst suminf_indicator)
    apply (auto simp add: disjoint_family_on_def space_stream_space split: split_indicator)
    done
  finally show ?thesis
    by simp
next
  assume ae: "\<not> (AE \<omega> in srw.T j. h k (j ## \<omega>) \<noteq> \<infinity>)"
  then have "(\<integral>\<^sup>+\<omega>. h k (j ## \<omega>) \<partial>srw.T j) = \<infinity>"
    using nn_integral_PInf_AE[of "\<lambda>\<omega>. h k (j ## \<omega>)" "srw.T j"] by (auto simp: ennreal_of_enat_eq_top)
  moreover have "(\<integral>\<^sup>+\<omega>. h k (j ## \<omega>) \<partial>srw.T j) \<le> (\<integral>\<^sup>+\<omega>. h i (j ## \<omega>) \<partial>srw.T j)"
    apply (rule nn_integral_mono_AE)
    using srw.AE_T_enabled
  proof (eventually_elim, simp)
    have *: "mono (\<lambda>F \<omega>. if HLD {k} \<omega> then 0 else eSuc (F (stl \<omega>)))"
      by (auto simp: mono_def le_fun_def)
    have **: "\<And>\<omega> j. srw.enabled j \<omega> \<Longrightarrow> j < k \<Longrightarrow> h k \<omega> \<le> h i \<omega>"
      apply (subst sfirst_eq_lfp)
    proof (induction rule: lfp_ordinal_induct[OF *])
      case (1 x \<omega> j)
      from "1.IH"[of "shd \<omega>" "stl \<omega>"] "1.prems" \<open>k \<le> i\<close>
      show ?case
        unfolding srw.enabled_iff[of j \<omega>]
        by (auto simp: eSuc_le_sfirst_iff) (simp_all add: HLD_iff)
    qed (auto intro: SUP_least)

    fix \<omega> show "srw.enabled j \<omega> \<Longrightarrow> h k (j ## \<omega>) \<le> h i (j ## \<omega>)"
      using \<open>j \<le> k\<close> \<open>k \<le> i\<close> by (simp add: sfirst_Stream **)
  qed
  ultimately show ?thesis
    by (simp add: top_unique)
qed

lemma H_eq: "H i j = (lfp (\<lambda>F i. if i = j then 0 else 1 + (F (i + 1) + F (i - 1)) / 2) i)"
proof -
  have cF: "sup_continuous (\<lambda>F i. (if i = j then 0 else 1 + (F (i + 1) + F (i - 1)) / 2)::ennreal)"
    by (intro order_continuous_intros)

  show ?thesis
  proof cases
    assume "i = j" then show ?thesis
      by (subst lfp_unfold[OF sup_continuous_mono[OF cF]])
         (simp add: sfirst_Stream zero_ennreal.rep_eq)
  next
    assume "i \<noteq> j"
    then have "H i j = 1 + lfp (\<lambda>F x. \<integral>\<^sup>+y. (F y + 1) * indicator (-{j}) y \<partial>srw x) i"
      by (simp add: sfirst_Stream nn_integral_add srw.sfirst_lfp)
    also have "\<dots> = (lfp (\<lambda>F x. \<integral>\<^sup>+y. (F y + 1) * indicator (-{j}) y \<partial>srw x) i + 1) * indicator (-{j}) i"
      using \<open>i \<noteq> j\<close> by (simp add: le_fun_def)
    also have "\<dots> = lfp (\<lambda>F x. ((\<integral>\<^sup>+y. F y \<partial>srw x) + 1) * indicator (-{j}) x) i"
      by (subst lfp_rolling[symmetric, where g="\<lambda>F y. (F y + 1) * indicator (-{j}) y"])
         (force simp: mono_def le_fun_def intro!: add_mono nn_integral_mono intro: max.coboundedI1 split: split_indicator)+
    also have "\<dots> = lfp (\<lambda>F i. if i = j then 0 else 1 + (F (i + 1) + F (i - 1)) / 2) i"
      by (intro arg_cong[where f="\<lambda>x. lfp x i"] ext)
         (auto simp: srw_def divide_ennreal_def field_simps)
    finally show ?thesis .
  qed
qed

lemma H_eq_top: assumes "i \<noteq> j" shows "H i j = top"
proof -
  have m_eq: "H i j = (if i = j then 0 else 1 + (H (i + 1) j + H (i - 1) j) / 2)" for i j
    apply (subst srw.nn_integral_T)
    apply simp
    apply (subst srw_def)
    apply (simp add: nn_integral_add divide_ennreal_def[symmetric] add_divide_distrib_ennreal)
    apply (simp add: add_divide_distrib_ennreal[symmetric])
    done
  have m_same[simp]: "H i i = 0" for i
    by (subst m_eq) simp
  have m_uminus[simp]: "H (-i) (-j) = H i j" for i j
    by (rule H_uminus)
  have m_split: "i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> H i j = H i k + H k j" for i j k
    using H_split[of i k j] by (simp add: eq_onp_def)
  have m_shift: "H (i + t) (j + t) = H i j" for i j t
    by (rule H_add)

  have m_plus: "H i (i + n) = n * H 0 1" for i :: int and n :: nat
  proof (induction n)
    case 0 then show ?case by simp
  next
    case (Suc n) then show ?case
      using m_split[of i "i + 1" "i + (1 + n)"] m_shift[of 0 i 1] m_shift[of i 1 "i + n"]
      by (simp add: field_simps)
  qed

  { fix i j :: int assume "i < j"
    then obtain n :: nat where j: "j = i + Suc n"
      by (auto simp add: zless_iff_Suc_zadd)
    then have "Suc n * H 0 1 = H i (i + Suc n)"
      unfolding m_plus by simp
    also have "\<dots> = 1 + (H (i + 1) (i + Suc n) + H (i - 1) (i + Suc n)) / 2"
      by (subst m_eq) simp
    also have "\<dots> = 1 + (H i (i + n) + H i (i + int (n + 2))) / 2"
      using m_shift[of i 1 "i + n"] m_shift[of i "-1" "i + n + 2"] by (simp add: field_simps)
    also have "\<dots> = 1 + (2 * of_nat (n + 1) * H 0 1) / 2"
      unfolding m_plus by (simp add: field_simps mult_2)
    also have "\<dots> = 1 + (((n + 1) * H 0 1) * 2) / 2"
      by (simp del: of_nat_add of_nat_Suc add: ac_simps)
    also have "\<dots> = 1 + Suc n * H 0 1"
      by (subst ennreal_mult_divide_eq) auto
    finally have "H 0 1 = top"
      by (cases "H 0 1" rule: ennreal_cases) (auto simp: ennreal_mult_eq_top_iff)
    then have "H i j = top"
      unfolding j m_plus by (simp add: ennreal_mult_eq_top_iff add_eq_0_iff_both_eq_0) }
  note inc = this
  moreover
  have "j < i \<Longrightarrow> H i j = top"
    using inc[of "-i" "-j"] unfolding m_uminus by simp
  ultimately show "H i j = top"
    using \<open>i \<noteq> j\<close> unfolding neq_iff by auto
qed

end

definition random_walk :: "int pgcl"
where
  "random_walk =
    Seq
      (Assign (\<lambda>i. return_pmf 10))
      (While (\<lambda>i. 0 < i)
             (Assign (\<lambda>i. map_pmf (\<lambda>True \<Rightarrow> i + 1 | False \<Rightarrow> i - 1) (bernoulli_pmf (1/2)))))"

lemma ert_random_walk:
  "ert random_walk 0 i = 1 + lfp (\<lambda>F i. 1 + (if 0 < i then 1 + (F (i + 1) + F (i - 1)) / 2 else 0)) (10::int)"
  by (auto simp: random_walk_def divide_ennreal_def distrib_left ac_simps fun_eq_iff
           intro!: arg_cong2[where f=lfp])

lemma ert_random_walk_top:
  "ert random_walk 0 i = top"
proof -
  have F: "mono (\<lambda>F i. (if i = 0 then 0 else 1 + (F (i + 1) + F (i - 1)) / 2)::ennreal)"
    by (auto simp: mono_def le_fun_def add_mono divide_ennreal_def mult_mono)
  have F': "mono (\<lambda>F i. 1 + (if 0 < i then 1 + (F (i + 1) + F (i - 1)) / 2 else 0)::ennreal)"
    by (auto simp: mono_def le_fun_def add_mono divide_ennreal_def mult_mono)
  have "\<And>i. 0 \<le> i \<Longrightarrow>
    lfp (\<lambda>F (i::int). (if i = 0 then 0 else 1 + (F (i + 1) + F (i - 1)) / 2)::ennreal) i \<le>
    lfp (\<lambda>F (i::int). 1 + (if 0 < i then 1 + (F (i + 1) + F (i - 1)) / 2 else 0)) i"
    apply (induction rule: lfp_ordinal_induct[OF F])
    apply (auto intro: SUP_least)
    apply (subst lfp_unfold[OF F'])
    apply (auto intro!: add_increasing[where a=1] add_mono mult_mono simp: divide_ennreal_def)
    done
  from this[of 10] H_eq_top[of 10 0] show ?thesis
    unfolding ert_random_walk H_eq by (simp add: top_unique)
qed

end
