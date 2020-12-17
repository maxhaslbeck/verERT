theory Recursive_PGCL
  imports "Markov_Models.Markov_Decision_Process"
begin

typedef (overloaded) ('a::order, 'b::order) mono_fun ("(_ \<Rightarrow>\<^sub>m /_)" [22, 21] 21) = "{f :: 'a \<Rightarrow> 'b. mono f}"
  by (auto simp: mono_def)

setup_lifting type_definition_mono_fun

instantiation mono_fun :: (order, complete_lattice) complete_lattice
begin

lift_definition less_eq_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> bool" is "op \<le>" .

definition less_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> bool"
where
  "less_mono_fun a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

lift_definition Sup_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) set \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b)" is "Sup"
  by (auto simp: mono_def le_fun_def intro!: SUP_mono)

lift_definition Inf_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) set \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b)" is "Inf"
  by (auto simp: mono_def le_fun_def intro!: INF_mono)

lift_definition sup_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b)" is "sup"
  by (auto simp: mono_def le_fun_def intro: le_supI1 le_supI2)

lift_definition inf_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b)" is "inf"
  by (auto simp: mono_def le_fun_def intro: le_infI1 le_infI2)

lift_definition top_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b)" is "top"
  by (auto simp: mono_def le_fun_def)

lift_definition bot_mono_fun :: "('a \<Rightarrow>\<^sub>m 'b)" is "bot"
  by (auto simp: mono_def le_fun_def)

instance
  apply standard
  apply (simp add: less_mono_fun_def)
  apply (transfer; auto intro: Sup_upper Sup_least Inf_lower Inf_greatest)+
  done
end

datatype ('s, 'n) pgcl =
    Skip
  | Abort
  | Assign "'s \<Rightarrow> 's pmf"
  | Seq "('s, 'n) pgcl" "('s, 'n) pgcl" ("_;;/ _"  [60, 61] 60)
  | Par "('s, 'n) pgcl" "('s, 'n) pgcl"
  | If "'s \<Rightarrow> bool" "('s, 'n) pgcl" "('s, 'n) pgcl"
  | Call "'n"

lift_definition wp_body ::
  "('n \<Rightarrow> ('s, 'n) pgcl) \<Rightarrow> (('s, 'n) pgcl \<Rightarrow> ('s \<Rightarrow> ennreal) \<Rightarrow>\<^sub>m ('s \<Rightarrow> ennreal)) \<Rightarrow>
    ('s, 'n) pgcl \<Rightarrow> ('s \<Rightarrow> ennreal) \<Rightarrow>\<^sub>m ('s \<Rightarrow> ennreal)"
is
  "\<lambda>D wp. \<lambda>
    Skip       \<Rightarrow> \<lambda>f s. f s
  | Abort      \<Rightarrow> \<lambda>f s. 0
  | Assign u   \<Rightarrow> \<lambda>f s. \<integral>\<^sup>+s'. f s' \<partial>u s
  | Seq c1 c2  \<Rightarrow> wp c1 \<circ> wp c2
  | Par c1 c2  \<Rightarrow> wp c1 \<squnion> wp c2
  | If b c1 c2 \<Rightarrow> \<lambda>f s. if b s then wp c1 f s else wp c2 f s
  | Call n     \<Rightarrow> wp (D n)"
  by (auto simp: mono_def le_fun_def intro!: nn_integral_mono intro: le_supI1 le_supI2 split: pgcl.split)

definition wp :: "('n \<Rightarrow> ('s, 'n) pgcl) \<Rightarrow> ('s, 'n) pgcl \<Rightarrow> ('s \<Rightarrow> ennreal) \<Rightarrow> ('s \<Rightarrow> ennreal)" where
  "wp D c = Rep_mono_fun (lfp (wp_body D) c)"

lemma mono_wp_body: "mono (wp_body D)"
  unfolding mono_def le_fun_def
  apply transfer
  apply (auto simp: le_fun_def intro: le_supI1 le_supI2 split: pgcl.split)
  subgoal for wp1 wp2 c1 c2 f s
    apply (rule le_funD[where x=s])
    apply (rule order_trans[where y="wp1 c1 (wp2 c2 f)"])
    apply (rule monoD[where f="wp1 c1"])
    apply simp
    apply (simp add: le_fun_def)
    apply (simp add: le_fun_def)
    done
  done

lemma mono_wp[simp]: "mono (wp D c)"
  using Rep_mono_fun[of "lfp (wp_body D) c"] by (simp add: wp_def)

lemma unfold_wp': "wp D c = Rep_mono_fun (wp_body D (Abs_mono_fun \<circ> wp D) c)"
  unfolding wp_def[abs_def]
  apply (subst lfp_unfold[OF mono_wp_body])
  apply (simp add: comp_def Rep_mono_fun_inverse)
  done

lemma unfold_wp: "wp D c = (case c
  of Skip \<Rightarrow> \<lambda>f s. f s
   | Abort \<Rightarrow> \<lambda>f s. 0
   | Assign u \<Rightarrow> \<lambda>f s. \<integral>\<^sup>+s'. f s' \<partial>u s
   | Seq c1 c2 \<Rightarrow> wp D c1 \<circ> wp D c2
   | Par c1 c2 \<Rightarrow> wp D c1 \<squnion> wp D c2
   | If b c1 c2 \<Rightarrow> \<lambda>f s. if b s then wp D c1 f s else wp D c2 f s
   | Call n \<Rightarrow> wp D (D n))"
  by (subst unfold_wp')
    (simp_all add: fun_eq_iff wp_body.rep_eq comp_def Rep_mono_fun_inverse Abs_mono_fun_inverse cong: if_cong split: pgcl.split)

lemma wp_Skip[simp]:   "wp D Skip = (\<lambda>f s. f s)"
  and wp_Abort[simp]:  "wp D Abort = (\<lambda>f s. 0)"
  and wp_Assign[simp]: "wp D (Assign u) = (\<lambda>f s. \<integral>\<^sup>+s'. f s' \<partial>u s)"
  and wp_Seq[simp]:    "wp D (Seq c1 c2) = wp D c1 \<circ> wp D c2"
  and wp_Par[simp]:    "wp D (Par c1 c2) = wp D c1 \<squnion> wp D c2"
  and wp_If[simp]:     "wp D (If b c1 c2) = (\<lambda>f s. if b s then wp D c1 f s else wp D c2 f s)"
  and wp_Call[simp]:   "wp D (Call n) = wp D (D n)"
  by (simp_all add: unfold_wp)



end