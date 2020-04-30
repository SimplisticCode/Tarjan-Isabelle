theory Dutch_National_Flag_Monad_Definitions_Lemmas
imports 
  "Dutch_National_Flag_Monad_Eisbach"
begin

section\<open>Aux. lemmas about values inside the array\<close>

text\<open>These proofs have been made to make Isabelle able to infer the correct value at position @{text i} in the array.
  The proof contains the same information in the assumptions that can be inferred from the conditional-statements and precondition.\<close>  
lemma value_must_be_one : "\<lbrakk>xs e ! i e  \<noteq> 0 ; xs e! i e \<noteq> 2 ; i e < length (xs e) ; set(xs e) \<subseteq> {0,1,2}\<rbrakk> \<Longrightarrow> xs e ! i e = 1"
  by (smt insertE insert_subset mk_disjoint_insert nth_mem singletonD)

lemma value_must_be_two_aux : "\<lbrakk>xs e ! i e  \<noteq> 0 ; xs e! i e \<noteq> 1 ; i e < length (xs e) ; set(xs e) \<subseteq> {0,1,2}\<rbrakk> \<Longrightarrow> xs e ! i e = 2"
  by (smt insertE insert_subset mk_disjoint_insert nth_mem singletonD)

lemma value_must_be_two_aux1 : "\<lbrakk>xs e! i e > 1 ; i e < length (xs e) ; set(xs e) \<subseteq> {0,1,2}\<rbrakk> \<Longrightarrow> xs e ! i e = 2"
  using value_must_be_one by force

lemma value_must_be_two : "\<lbrakk>xs e ! i e  > 0 ; xs e! i e > 1 ; i e < length (xs e) ; set(xs e) \<subseteq> {0,1,2}\<rbrakk> \<Longrightarrow> xs e ! i e = 2"
  using nat_neq_iff value_must_be_two_aux by blast

lemma value_must_be_one_aux : "\<lbrakk>\<not>xs e ! i e  > 1 ; \<not>xs e! i e < 1 ; i e < length (xs e) ; set(xs e) \<subseteq> {0,1,2}\<rbrakk> \<Longrightarrow> xs e ! i e = 1"
  by linarith

section\<open>Inc lowbound - proof\<close>
text\<open>Inc lowbound will keep the relationship between variables and both the @{text i} and @{text low} variables will be increased\<close>
lemma inc_lowbound_spec: "spec (inc_lowbound_pre e) inc_lowbound (GG (inc_lowbound_post e))"
  unfolding inc_lowbound_pre_def loop_update_action_pre_def dnfp_variables_invariants_def GG_def inc_lowbound_post_def loop_update_action_post_def dnfp_post_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
  apply(rewrite_env simps: swap_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
  apply(rewrite_env simps: i_Env_def)
  apply(rewrite_env simps: low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
  apply(rewrite_env simps: xs_Env_def swap_def)
  apply(all_Get_Seq)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(all_Get_Seq)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(all_Get_Seq)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y = high e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y = high e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. low y = low e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. low y = low e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y = i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y > i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y - i y \<le> high e - i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y - i y \<le> high e - i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply (linarith)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply (metis (no_types, hide_lams) Multiset.mset_swap le_less_trans less_le_trans)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. high y - i y = high e - i e \<and> high e > i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. Suc(high y - i y) = high e - i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. i y \<ge> i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. i y > i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  by(simp add: spec_def put_def get_state_def put_state_def low_Env_def)

subsection\<open>Invariants - inc lowbound\<close>
text\<open>These proofs show that the invariants on the ranges are kept by a @{text inc_lowbound_action}\<close>
lemma inc_lowbound_invariantRed: "spec inc_lowbound_inv1 inc_lowbound (GG dnfp_inv1)"
  unfolding inc_lowbound_inv1_def loop_update_action_pre_def  GG_def loop_update_action_inv1_def dnfp_inv1_def low_invariant_is_0_Env_def dnfp_variables_invariants_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. i s < high s \<and>
                 low s \<le> i s \<and>
                 high s \<le> length (xs s) \<and>
                 set (xs s) \<subseteq> {0, 1, 2} \<and>
                 (\<forall>x \<le> low s. xs s ! x = 0))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply (smt length_list_update less_le_trans nth_list_update order.not_eq_order_implies_strict set_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. i s \<le> high s \<and>
                 low s < i s \<and>
                 high s \<le> length (xs s) \<and>
                 set (xs s) \<subseteq> {0, 1, 2} \<and>
                 (\<forall>x\<le>low s. xs s ! x = 0))"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  by (simp add: spec_def put_def put_state_def get_state_def low_Env_def)

lemma inc_lowbound_invariantWhite: "spec inc_lowbound_inv2 inc_lowbound (GG dnfp_inv2)"
  unfolding inc_lowbound_inv2_def loop_update_action_inv2_def  inc_lowbound_inv2_def loop_update_action_pre_def dnfp_inv2_def GG_def invariant_low_to_j_is_1_Env_def dnfp_variables_invariants_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. i s < high s \<and>
                 low s \<le> i s \<and>
                 high s \<le> length (xs s) \<and>
                 set (xs s) \<subseteq> {0, 1, 2} \<and>
                 (\<forall>x. low s < x \<and> x \<le> i s \<longrightarrow> xs s ! x = 1))"])
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
  apply (smt le_less less_le_trans nth_list_update set_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. i s \<le> high s \<and>
                 low s < i s \<and>
                 high s \<le> length (xs s) \<and>
                 set (xs s) \<subseteq> {0, 1, 2} \<and>
                 (\<forall>x. low s < x \<and> x < i s \<longrightarrow> xs s ! x = 1))"])
  apply (simp add: spec_def put_def put_state_def  get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  by (simp add: spec_def put_def put_state_def  get_state_def low_Env_def)

lemma inc_lowbound_invariantBlue: "spec inc_lowbound_inv3  inc_lowbound (GG dnfp_inv3)"
  unfolding  inc_lowbound_inv3_def loop_update_action_inv3_def loop_update_action_pre_def dnfp_inv3_def  GG_def high_invariant_is_2_Env_def dnfp_variables_invariants_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. 
                       low s \<le> i s \<and>
                       high s \<le> length (xs s) \<and>
                       set (xs s) \<subseteq> {0, 1, 2} \<and>
                       i s < high s \<and>
                       (\<forall>x. high s \<le> x \<and> x < length (xs s) \<longrightarrow> xs s ! x = 2))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply (smt less_le_trans not_less set_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x s. i s \<le> high s \<and>
                 low s < i s \<and>
                 high s \<le> length (xs s) \<and>
                 set (xs s) \<subseteq> {0, 1, 2} \<and>
                 (\<forall>x. high s \<le> x \<and> x < length (xs s) \<longrightarrow> xs s ! x = 2))"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  by (simp add: spec_def put_def put_state_def get_state_def low_Env_def)

text\<open>All invariants are preserved\<close>
lemma inc_lowbound_invariants: "spec inc_lowbound_inv_pre  inc_lowbound (GG dnfp_inv)"
  unfolding inc_lowbound_inv_pre_def GG_def dnfp_inv_def loop_update_action_inv_def
  by (smt GG_def inc_lowbound_inv1_def inc_lowbound_inv2_def inc_lowbound_inv3_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def spec_def split_beta')

section\<open>Dec highbound proof\<close>                                          
lemma dec_highbound_spec: "spec (dec_highbound_pre e) dec_highbound (GG (dec_highbound_post e))"
  unfolding dec_highbound_pre_def dnfp_variables_invariants_def dnfp_post_def loop_update_action_pre_def GG_def dec_highbound_post_def loop_update_action_post_def
  apply(simp_all add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < length (xs y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < high e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e = i y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. xs y ! i y = 2 \<and> high y < length(xs y) \<and> high y \<ge> i y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  using less_le_trans value_must_be_two_aux1 apply auto[1]
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y \<le> high e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. low e \<le> low y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e \<le> i y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y - i y \<le> high e - i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply (simp add: diff_le_mono2)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. mset (xs e) = mset (xs y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def swap_def xs_Env_def)
  apply (simp add: mset_swap)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. Suc(high y - i y) = high e - i e \<and> high e > i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  
subsection\<open>Invariants - dec highbound\<close>
text\<open>These proofs show that the invariants on the ranges are kept by a @{text dec_highbound_action}\<close>
lemma dec_highbound_invariantRed: "spec dec_highbound_inv1 dec_highbound (GG dnfp_inv1)"
    unfolding dec_highbound_inv1_def dec_highbound_inv1_def loop_update_action_inv1_def dnfp_inv1_def dnfp_variables_invariants_def loop_update_action_pre_def GG_def low_invariant_is_0_Env_def
    apply(simp_all add: dec_highbound_def)
    apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>x e. i e \<le> high e \<and>
                 low e \<le> i e \<and>
                 high e \<le> length (xs e) \<and>
                 set (xs e) \<subseteq> {0, 1, 2} \<and> Suc 0 < xs e ! i e \<and> (\<forall>x < low e. xs e ! x = 0))"])
    apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply linarith
    apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
    by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)


lemma dec_highbound_invariantWhite: "spec dec_highbound_inv2 dec_highbound (GG dnfp_inv2)"
    unfolding dec_highbound_inv2_def dec_highbound_inv2_def loop_update_action_inv2_def dnfp_inv2_def  dnfp_variables_invariants_def loop_update_action_pre_def GG_def invariant_low_to_j_is_1_Env_def
    apply(simp_all add: dec_highbound_def)
    apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>x e. i e \<le> high e \<and>
                 low e \<le> i e \<and>
                 high e \<le> length (xs e) \<and>
                 set (xs e) \<subseteq> {0, 1, 2} \<and> Suc 0 < xs e ! i e \<and> (\<forall>x. low e \<le> x \<and> x < i e \<longrightarrow> xs e ! x = Suc 0))"])
    apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply linarith
    apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
    by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)

lemma dec_highbound_invariantBlue: "spec dec_highbound_inv3 dec_highbound (GG dnfp_inv3)"
    unfolding dec_highbound_inv3_def dec_highbound_inv3_def loop_update_action_inv3_def dnfp_inv3_def dnfp_variables_invariants_def loop_update_action_pre_def GG_def high_invariant_is_2_Env_def
    apply(simp_all add: dec_highbound_def)
    apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>x e. i e \<le> high e \<and>
                 low e \<le> i e \<and>
                 high e \<le> length (xs e) \<and>
                 set (xs e) \<subseteq> {0, 1, 2} \<and> Suc 0 < xs e ! i e \<and> (\<forall>x. high e < x \<and> x < length (xs e) \<longrightarrow> xs e ! x = 2))"])
    apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply force
    apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
    apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
    by (smt One_nat_def leD le_eq_less_or_eq le_less_trans length_list_update less_numeral_extra(2) nth_list_update value_must_be_two_aux)

lemma dec_highbound_invariants: "spec dec_highbound_inv dec_highbound (GG dnfp_inv)"
  unfolding dec_highbound_inv_def loop_update_action_inv_def GG_def dnfp_inv_def
  by (smt GG_def case_prodD dec_highbound_inv1_def dec_highbound_inv2_def dec_highbound_inv3_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def spec_def split_cong)

section\<open>Inc index proof\<close>
lemma inc_index_spec: "spec (inc_index_pre e) inc_index (GG (inc_index_post e))"
  unfolding inc_index_pre_def dnfp_variables_invariants_def dnfp_post_def loop_update_action_pre_def GG_def inc_index_post_def loop_update_action_post_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI;simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply linarith
  by linarith

subsection\<open>Invariants - inc index\<close>
text\<open>These proofs show that the invariants on the ranges are kept by an @{text inc_index}-action. 
  It can be noted that these proofs are straightforward since the definition only contains one put-statement. 
And nothing follows the put-statement. It is therefore not necessary to introduce the seq-rule.)\<close>
lemma inc_index_invariantRed: "spec inc_index_inv1 inc_index (GG dnfp_inv1)"
  unfolding inc_index_inv1_def loop_update_action_inv1_def dnfp_variables_invariants_def dnfp_inv1_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)
                               
lemma inc_index_invariantWhite: "spec inc_index_inv2 inc_index (GG dnfp_inv2)"
  unfolding inc_index_inv2_def loop_update_action_inv2_def dnfp_variables_invariants_def dnfp_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def i_Env_def put_def get_state_def put_state_def)
  using le_eq_less_or_eq by fastforce

lemma inc_index_invariantBlue: "spec inc_index_inv3 inc_index (GG dnfp_inv3)"
  unfolding inc_index_inv3_def loop_update_action_inv3_def  dnfp_variables_invariants_def dnfp_inv3_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)

lemma inc_index_invariants: "spec inc_index_inv inc_index (GG dnfp_inv)"
  unfolding inc_index_inv_def dnfp_inv_def GG_def loop_update_action_inv_def
  by (smt GG_def inc_index_inv1_def inc_index_inv2_def inc_index_inv3_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def spec_def split_beta')

section\<open>Loop update action - proofs\<close>
text\<open>This proofs shows that the loop-update-action preserves the relationship on the variables. This proof can be rewritten to make use of the lemmas established in the file above.\<close>
lemma loop_update_action_spec: "spec (loop_update_action_pre_aux e) loop_update_action (GG (loop_update_action_post e))"
  unfolding loop_update_action_pre_aux_def GG_def loop_update_action_post_def loop_update_action_pre_def dnfp_variables_invariants_def dnfp_post_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
  apply (intro cond_rule)
  apply(simp add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
  apply (simp add: spec_def put_def put_state_def  get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y = i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y > i e)"])
  apply (simp add: spec_def put_def put_state_def  get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def  get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y < high y \<and> i y = i e \<and> high y = high e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y - i y < high e - i e)"])
  apply (simp add: spec_def put_def put_state_def  get_state_def i_Env_def)
  apply (linarith)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def  get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. mset(xs e) = mset(xs y))"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply (simp add: Multiset.mset_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. mset(xs e) = mset(xs y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def  get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. high y - i y = high e - i e \<and> high e > i e)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (intro seq_rule[of _ _ "(\<lambda>x y. Suc(high y - i y) = high e - i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply (simp add: spec_def put_def put_state_def get_state_def low_Env_def)

  apply(simp add: dec_highbound_def)
  apply(intro conj_rule_right)
  apply (intro get_rule; intro allI; simp)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
  apply (simp add: spec_def put_def get_state_def put_state_def high_Env_def swap_def)
  apply (rule allI; simp; intro get_rule; rule allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y < high e)"]) 
  apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
  apply (intro allI; simp)
  apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"]) 
  apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
  apply (intro allI; simp)
  apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"]) 
  apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
  apply (intro allI; simp)
  apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y < high e - i e)"]) 
  apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
  apply(linarith)
  apply(intro allI; simp)
  apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (intro get_rule; intro allI; simp)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. mset(xs e) = mset(xs y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
  apply (simp add: Multiset.mset_swap)
  apply(intro get_rule; intro allI; simp)

  apply (intro seq_rule[of _ _ "(\<lambda>x y. Suc(high y - i y) = high e - i e \<and> high e > i e)"])
  apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply(simp add: inc_index_def)
  apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
  apply (simp add: diff_le_mono2)
  by (simp add: Suc_diff_Suc)

subsection\<open>Invariants - Loop update action \<close>                                                       
lemma loop_update_action_invariantRed: "spec loop_update_action_inv1 loop_update_action (GG dnfp_inv1)"
   unfolding loop_update_action_inv1_def loop_update_action_inv1_def dnfp_variables_invariants_def dnfp_inv1_def  loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
   apply(simp add: loop_update_action_def)
   apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule)
   apply(simp add: inc_lowbound_def)
   apply (intro get_rule; intro allI; simp)
   apply(intro seq_rule[of _ _ "(\<lambda>x e. i e < high e \<and>
                                low e \<le> i e \<and>
                                high e \<le> length (xs e) \<and> set (xs e) \<subseteq> {0, 1, 2} \<and> (\<forall>x\<le>low e. xs e ! x = 0))"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
   apply (smt le_antisym le_eq_less_or_eq le_trans length_list_update nth_list_update_eq nth_list_update_neq)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
   apply(intro seq_rule[of _ _ "(\<lambda>x e. i e \<le> high e \<and>
               low e < i e \<and>
               high e \<le> length (xs e) \<and> set (xs e) \<subseteq> {0, 1, 2} \<and> (\<forall>x\<le>low e. xs e ! x = 0))"])
   apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
   apply (simp add: spec_def put_def put_state_def get_state_def low_Env_def)
   apply(simp add: dec_highbound_def)
   apply (intro get_rule; intro allI; simp)
   apply(intro seq_rule[of _ _ "(\<lambda>_ e. i e \<le> high e \<and>
               low e \<le> i e \<and>
               high e \<le> length (xs e) \<and> set (xs e) \<subseteq> {0, 1, 2} \<and> (\<forall>x<low e. xs e ! x = 0))"]) 
   apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
   apply(linarith)
   apply(intro allI; simp)
   apply (intro get_rule; intro allI; simp)
   apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
   apply(simp add: inc_index_def)
   apply (intro get_rule; intro allI; simp)
   by (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)

text\<open>The following proofs are mostly done using the already established lemmas of the definitions inside loop update action. This can be seen from the lemmas used inside smt-statement\<close>
lemma loop_update_action_invariantWhite: "spec loop_update_action_inv2 loop_update_action (GG dnfp_inv2)"
   unfolding loop_update_action_inv2_def GG_def
   apply(simp add: loop_update_action_def)
   apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule; simp)
   apply (smt GG_def case_prodD case_prodI2  inc_lowbound_inv2_def inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_inv2_def spec_def)
   apply (smt GG_def One_nat_def dec_highbound_inv2_def dec_highbound_invariantWhite loop_update_action_inv2_def spec_def split_beta')
   by (smt GG_def One_nat_def Suc_less_eq inc_index_inv2_def inc_index_invariantWhite less_Suc_eq loop_update_action_inv2_def spec_def split_beta')
   
lemma loop_update_action_invariantBlue: "spec loop_update_action_inv3 loop_update_action (GG dnfp_inv3)"
   unfolding loop_update_action_inv3_def GG_def 
   apply(simp add: loop_update_action_def)
   apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule;simp)
   apply (smt GG_def case_prodD case_prodI2  inc_lowbound_inv3_def inc_lowbound_invariantBlue less_numeral_extra(1) loop_update_action_inv3_def spec_def)
   apply (smt GG_def One_nat_def  dec_highbound_inv3_def dec_highbound_invariantBlue loop_update_action_inv3_def spec_def split_beta')
   by (smt GG_def One_nat_def Suc_less_eq  inc_index_inv3_def inc_index_invariantBlue less_Suc_eq loop_update_action_inv3_def spec_def split_beta')

lemma loop_update_action_invariants: "spec loop_update_action_inv loop_update_action (GG dnfp_inv)"
  unfolding loop_update_action_inv_def GG_def loop_update_action_inv_def dnfp_inv_def
  by (smt GG_def case_prodD case_prodI2 loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def loop_update_action_invariantBlue loop_update_action_invariantRed loop_update_action_invariantWhite spec_def)
end