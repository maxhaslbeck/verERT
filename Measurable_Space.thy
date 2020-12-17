theory Measurable_Space
  imports Probability
begin

subsection \<open>Typeclass for measurable spaces\<close>

lemma borel_measurable_max[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  shows "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  by (intro borel_measurableI_less) auto

lemma borel_measurable_min[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  shows "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
  by (intro borel_measurableI_less) (auto simp: min_less_iff_disj)

lemma borel_measurable_SUP[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{countable_complete_lattice, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. SUP i:I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_greater) (simp add: less_ccSUP_iff)

lemma borel_measurable_INF[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{countable_complete_lattice, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i:I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_less) (simp add: ccINF_less_iff)

class measurable_space =
  fixes measurable_space :: "'a measure"
  assumes space_measurable_space[simp]: "space measurable_space = UNIV"

class borel_space = topological_space + measurable_space +
  assumes measurable_space_eq_borel: "measurable_space = borel"

instantiation real :: borel_space
begin

definition measurable_space_real :: "real measure"
  where "(measurable_space :: real measure) = borel"

instance by standard (simp_all add: measurable_space_real_def borel_def)

end

instantiation ereal :: borel_space
begin

definition measurable_space_ereal :: "ereal measure"
  where "(measurable_space :: ereal measure) = borel"

instance by standard (simp_all add: measurable_space_ereal_def borel_def)

end

instantiation ennreal :: borel_space
begin

definition measurable_space_ennreal :: "ennreal measure"
  where "(measurable_space :: ennreal measure) = borel"

instance by standard (simp_all add: measurable_space_ennreal_def borel_def)

end

instantiation stream :: (measurable_space) measurable_space
begin

definition measurable_space_stream :: "'a stream measure"
  where "(measurable_space :: 'a stream measure) = stream_space measurable_space"

instance by standard (simp add: measurable_space_stream_def space_stream_space)

end

instantiation bool :: borel_space
begin

definition measurable_space_bool :: "bool measure"
  where "(measurable_space :: bool measure) = borel"

instance by standard (simp_all add: measurable_space_bool_def borel_def)

end

instantiation enat :: borel_space
begin

definition measurable_space_enat :: "enat measure"
  where "(measurable_space :: enat measure) = borel"

instance by standard (simp_all add: measurable_space_enat_def borel_def)

end

instantiation nat :: borel_space
begin

definition measurable_space_nat :: "nat measure"
  where "(measurable_space :: nat measure) = borel"

instance by standard (simp_all add: measurable_space_nat_def borel_def)

end

subsection \<open>Type of measurable functions\<close>

typedef (overloaded) ('a, 'b) measurable_fun =
  "measurable measurable_space measurable_space :: ('a::measurable_space \<Rightarrow> 'b::measurable_space) set"
  by (intro exI[of _ "\<lambda>x. undefined"]) auto
setup_lifting type_definition_measurable_fun

instantiation measurable_fun :: (measurable_space, "{order, measurable_space}") order
begin

lift_definition less_eq_measurable_fun :: "('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun \<Rightarrow> bool"
  is "op \<le>" .

lift_definition less_measurable_fun :: "('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun \<Rightarrow> bool"
  is "op <" .

instance
  by standard (transfer ; auto)+
end

instantiation measurable_fun :: (measurable_space, "{order_bot, measurable_space}") order_bot
begin

lift_definition bot_measurable_fun :: "('a, 'b) measurable_fun" is "bot"
  by (simp add: bot_fun_def)

instance
  proof qed (transfer; auto)
end

instantiation measurable_fun :: (measurable_space, "{order_top, measurable_space}") order_top
begin

lift_definition top_measurable_fun :: "('a, 'b) measurable_fun" is "top"
  by (simp add: top_fun_def)

instance
  proof qed (transfer; auto)
end

instantiation measurable_fun :: (measurable_space, "{second_countable_topology, linorder_topology, borel_space}") lattice
begin

lift_definition sup_measurable_fun :: "('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun"
  is "\<lambda>f g x. max (f x) (g x)" by (auto simp: measurable_space_eq_borel)

lift_definition inf_measurable_fun :: "('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun \<Rightarrow> ('a, 'b) measurable_fun"
  is "\<lambda>f g x. min (f x) (g x)" by (auto simp: measurable_space_eq_borel)

instance
  by standard (transfer; auto simp: le_fun_def)+
end

instantiation measurable_fun :: (measurable_space, "{second_countable_topology, countable_complete_lattice, linorder_topology, borel_space}") countable_complete_lattice
begin

lift_definition Sup_measurable_fun :: "('a, 'b) measurable_fun set \<Rightarrow> ('a, 'b) measurable_fun"
  is "\<lambda>A x. if countable A then SUP f:A. f x else top"
proof -
  fix A :: "('a \<Rightarrow> 'b) set" assume "\<And>f. f \<in> A \<Longrightarrow> f \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
  then show "(\<lambda>x. if countable A then SUP f:A. f x else top) \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
    by (cases "countable A") (auto simp: measurable_space_eq_borel)
qed

lift_definition Inf_measurable_fun :: "('a, 'b) measurable_fun set \<Rightarrow> ('a, 'b) measurable_fun"
  is "\<lambda>A x. if countable A then INF f:A. f x else bot"
proof -
  fix A :: "('a \<Rightarrow> 'b) set" assume "\<And>f. f \<in> A \<Longrightarrow> f \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
  then show "(\<lambda>x. if countable A then INF f : A. f x else bot) \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
    by (cases "countable A") (auto simp: measurable_space_eq_borel)
qed

instance
  by standard
     (transfer; auto simp add: le_fun_def intro: ccSUP_least ccSUP_upper ccINF_lower ccINF_greatest)+
end

lift_definition "integral_mf" :: "'a::measurable_space measure \<Rightarrow> ('a, ennreal) measurable_fun \<Rightarrow> ennreal" is
  nn_integral .

definition "rel_ne_countable = eq_onp (\<lambda>X. X \<noteq> {} \<and> countable X)"

lemma rel_ne_countable_UNIV_nat [transfer_rule]: "rel_ne_countable UNIV (UNIV::nat set)"
  by (auto simp: rel_ne_countable_def eq_onp_def)

lemma SUP_ennreal_transfer [transfer_rule]:
  "rel_fun rel_ne_countable (rel_fun (rel_fun op = pcr_ennreal) pcr_ennreal) SUPREMUM SUPREMUM"
  unfolding rel_fun_def rel_ne_countable_def eq_onp_def
  apply (auto simp: ennreal.pcr_cr_eq cr_ennreal_def Sup_ennreal.rep_eq)
  apply (subst (asm) max.absorb2)
  apply (auto intro: enn2ereal_nonneg SUP_upper2)
  done

lemma less_eq_measurable_ennreal_transfer[transfer_rule]:
  "rel_fun (pcr_measurable_fun op = pcr_ennreal) (rel_fun (pcr_measurable_fun op = pcr_ennreal) op =) op \<le> op \<le>"
  by (auto simp: rel_fun_def pcr_measurable_fun_def cr_measurable_fun_def le_fun_def cr_ennreal_def
                 ennreal.pcr_cr_eq less_eq_ennreal.rep_eq[symmetric] less_eq_measurable_fun.rep_eq)

lemma SUP_measurable_ennreal_transfer [transfer_rule]:
  fixes Q
  assumes *: "rel_fun (rel_ne_countable :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool) (rel_fun (rel_fun op = R) R) SUPREMUM SUPREMUM"
  defines "M \<equiv> pcr_measurable_fun Q R"
  shows "rel_fun (rel_ne_countable :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool) (rel_fun (rel_fun op = M) M) SUPREMUM SUPREMUM"
proof -
  have M: "M f g \<longleftrightarrow> (\<forall>x y. Q x y \<longrightarrow> R (f x) (Rep_measurable_fun g y))" for f g
    by (auto simp: M_def pcr_measurable_fun_def cr_measurable_fun_def
      ennreal.pcr_cr_eq cr_ennreal_def rel_fun_def relcompp.simps )
  show ?thesis
    unfolding rel_fun_def rel_ne_countable_def eq_onp_def Sup_measurable_fun.rep_eq M
    by (auto intro!: rel_funD[OF *, THEN rel_funD] simp: rel_ne_countable_def eq_onp_def)
qed

lemma rel_fun_pcr_ennreal_iff: "rel_fun op = pcr_ennreal f g \<longleftrightarrow> f = enn2ereal \<circ> g"
  by (auto simp: rel_fun_def ennreal.pcr_cr_eq cr_ennreal_def)

lemma sup_continuous_integral_mf:
  assumes [simp, measurable_cong]: "sets M = sets measurable_space"
  shows "sup_continuous (integral_mf M)"
  unfolding sup_continuous_def incseq_def
proof (transfer fixing: M, clarsimp simp: rel_fun_pcr_ennreal_iff)
  fix C :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assume "\<forall>i. \<exists>f. C i = enn2ereal \<circ> f \<and> f \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
  then obtain F where C: "\<And>i. C i = enn2ereal \<circ> F i" and F: "\<And>i. F i \<in> measurable_space \<rightarrow>\<^sub>M measurable_space"
    by metis
  assume "\<forall>m n. m \<le> n \<longrightarrow> C m \<le> C n"
  then show "integral\<^sup>N M (SUP x. C x) = (SUP i. integral\<^sup>N M (C i))"
    unfolding C using F
    by (subst nn_integral_monotone_convergence_SUP[symmetric])
       (auto simp: incseq_def o_def measurable_space_eq_borel
             cong: measurable_cong_sets intro!: nn_integral_cong)
qed

end
