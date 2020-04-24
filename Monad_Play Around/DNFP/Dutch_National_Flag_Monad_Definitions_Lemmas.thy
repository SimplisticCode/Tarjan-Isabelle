theory Dutch_National_Flag_Monad_Definitions_Lemmas
imports 
  "Dutch_National_Flag_Monad_Definitions"
begin

section\<open>Auxilarry lemmas\<close>

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

definition sorted_dnfp_pre where
 "sorted_dnfp_pre e \<equiv> i e = 0
                    \<and> low e = 0
                    \<and> high e = length (xs e)"

lemma sorted_dnfp_aux1: "\<lbrakk>sorted_dnfp_pre e\<rbrakk> \<Longrightarrow> low_invariant_is_0_Env e"
  unfolding sorted_dnfp_pre_def  low_invariant_is_0_Env_def
  by simp

lemma sorted_dnfp_aux2: "\<lbrakk>sorted_dnfp_pre e\<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1_Env e"
  unfolding sorted_dnfp_pre_def  invariant_low_to_j_is_1_Env_def
  by simp

lemma sorted_dnfp_aux3: "\<lbrakk>sorted_dnfp_pre e\<rbrakk> \<Longrightarrow> high_invariant_is_2_Env e"
  unfolding sorted_dnfp_pre_def  high_invariant_is_2_Env_def
  by simp

lemma sorted_dnfp: "\<lbrakk>sorted_dnfp_pre e\<rbrakk> \<Longrightarrow> invariants_Env e"
  unfolding sorted_dnfp_pre_def  invariants_Env_def
  by (simp add: invariant_low_to_j_is_1_Env_def low_invariant_is_0_Env_def sorted_dnfp_aux3 sorted_dnfp_pre_def)

definition sorted_array :: "env \<Rightarrow> bool" where
  "sorted_array e \<equiv> invariants_Env e 
                  \<and> set(xs e) = {0,1,2}
                  \<and> low e \<le> i e
                  \<and> i e = high e
                  \<and> high e \<le> length (xs e)"

lemma sorted_aux: "\<lbrakk>sorted_array e\<rbrakk> \<Longrightarrow> sorted (xs e)"
  unfolding sorted_array_def invariants_Env_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def low_invariant_is_0_Env_def
  by (smt Suc_1 Suc_leD less_le_trans nat_le_linear not_less not_one_le_zero sorted_iff_nth_mono)
  

lemma inc_lowbound_spec: "spec (inc_lowbound_pre e) inc_lowbound (GG (inc_lowbound_post e))"
  unfolding inc_lowbound_pre_def loop_update_action_pre_def dnfp_precondition_def GG_def inc_lowbound_post_def loop_update_action_post_def dnfp_post_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
         apply(intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
          apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
  apply(intro allI; simp)
         apply(intro get_rule; intro allI)
         apply (intro seq_rule[of _ _ "(\<lambda>_ y. high e = high y)"])
          apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
          apply (simp add: spec_def put_def get_def return_def put_state_def swap_def get_state_def low_Env_def)
  apply (intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
          apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
        apply(intro allI; simp)
        apply(intro get_rule; intro allI)
        apply(intro seq_rule[of _ _ "(\<lambda>_ y. low e = low y)"])
          apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
        apply(intro allI; simp)
        apply(intro get_rule; intro allI)
        apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
       apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
        apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
       apply(intro allI)
  apply(intro get_rule; intro allI; simp)
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

subsubsection\<open>Invariants\<close>
definition inc_lowbound_inv1_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv1_aux e \<equiv> inc_lowbound_inv1 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

lemma inc_lowbound_invariantRed: "spec inc_lowbound_inv1_aux inc_lowbound (GG inc_lowbound_inv1)"
  unfolding inc_lowbound_inv1_aux_def inc_lowbound_inv1_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def dnfp_precondition_def
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

definition inc_lowbound_inv2_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv2_aux e \<equiv> inc_lowbound_inv2 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

lemma inc_lowbound_invariantWhite: "spec inc_lowbound_inv2_aux inc_lowbound (GG inc_lowbound_inv2)"
  unfolding inc_lowbound_inv2_aux_def inc_lowbound_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def dnfp_precondition_def
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

definition inc_lowbound_inv3_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv3_aux e \<equiv> inc_lowbound_inv3 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

lemma inc_lowbound_invariantBlue: "spec inc_lowbound_inv3_aux  inc_lowbound (GG inc_lowbound_inv3)"
  unfolding inc_lowbound_inv3_aux_def inc_lowbound_inv3_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def dnfp_precondition_def
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

definition inc_lowbound_inv :: "env \<Rightarrow> bool" where
"inc_lowbound_inv s \<equiv> (inc_lowbound_inv3 s \<and> inc_lowbound_inv2 s \<and> inc_lowbound_inv1 s)"

definition inc_lowbound_inv_pre :: "env \<Rightarrow> bool" where
"inc_lowbound_inv_pre s \<equiv> (inc_lowbound_inv s \<and> loop_update_action_pre s \<and> xs s ! i s < 1)"

lemma inc_lowbound_invariants: "spec inc_lowbound_inv_pre  inc_lowbound (GG inc_lowbound_inv)"
  by (smt GG_def case_prodD case_prodI2 inc_lowbound_inv1_aux_def inc_lowbound_inv2_aux_def inc_lowbound_inv3_aux_def inc_lowbound_inv_def inc_lowbound_inv_pre_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite spec_def)

subsection\<open>Dec_highbound Invariants\<close>                                          
lemma dec_highbound_spec: "spec (dec_highbound_pre e) dec_highbound (GG (dec_highbound_post e))"
  unfolding dec_highbound_pre_def dnfp_precondition_def dnfp_post_def loop_update_action_pre_def GG_def dec_highbound_post_def loop_update_action_post_def
  apply(simp_all add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
   apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < length (xs y))"])
       apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
  apply linarith
           apply(intro allI; simp)
           apply(intro get_rule; intro allI; simp)
             apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  apply (simp add: length_swap)
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
      apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
         apply (simp add: Dutch_National_Flag_Monad_Definitions.mset_swap)
   apply (intro seq_rule[of _ _ "(\<lambda>x y. Suc(high y - i y) = high e - i e \<and> high e > i e)"])
         apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
        apply linarith
   apply(intro allI; simp)
   apply(intro get_rule; intro allI; simp)
        by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
  

definition dec_highbound_inv1_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv1_aux e \<equiv> dec_highbound_inv1 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

subsubsection\<open>Invariants\<close>
lemma dec_highbound_invariantRed: "spec dec_highbound_inv1_aux dec_highbound (GG dec_highbound_inv1)"
    unfolding dec_highbound_inv1_aux_def dec_highbound_inv1_def dnfp_precondition_def loop_update_action_pre_def GG_def low_invariant_is_0_Env_def
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

definition dec_highbound_inv2_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv2_aux e \<equiv> dec_highbound_inv2 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

lemma dec_highbound_invariantWhite: "spec dec_highbound_inv2_aux dec_highbound (GG dec_highbound_inv2)"
    unfolding dec_highbound_inv2_aux_def dec_highbound_inv2_def dnfp_precondition_def loop_update_action_pre_def GG_def invariant_low_to_j_is_1_Env_def
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

definition dec_highbound_inv3_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv3_aux e \<equiv> dec_highbound_inv3 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

lemma dec_highbound_invariantBlue: "spec dec_highbound_inv3_aux dec_highbound (GG dec_highbound_inv3)"
    unfolding dec_highbound_inv3_aux_def dec_highbound_inv3_def dnfp_precondition_def loop_update_action_pre_def GG_def high_invariant_is_2_Env_def
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

definition dec_highbound_inv :: "env \<Rightarrow> bool" where
"dec_highbound_inv s \<equiv> (dec_highbound_inv3 s \<and> dec_highbound_inv2 s \<and> dec_highbound_inv1 s)"

definition dec_highbound_inv_aux :: "env \<Rightarrow> bool" where
"dec_highbound_inv_aux s \<equiv> (dec_highbound_inv s \<and>  loop_update_action_pre s \<and> xs s ! i s > 1 )"

lemma dec_highbound_invariants: "spec dec_highbound_inv_aux dec_highbound (GG dec_highbound_inv)"
  by (smt GG_def case_prodD case_prodI2 dec_highbound_inv1_aux_def dec_highbound_inv2_aux_def dec_highbound_inv3_aux_def dec_highbound_inv_aux_def dec_highbound_inv_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite spec_def)

subsection\<open>Inc_index Invariants\<close>
lemma inc_index_spec: "spec (inc_index_pre e) inc_index (GG (inc_index_post e))"
  unfolding inc_index_pre_def dnfp_precondition_def dnfp_post_def loop_update_action_pre_def GG_def inc_index_post_def loop_update_action_post_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI;simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def i_Env_def)
   apply linarith
  by linarith

subsubsection\<open>Invariants\<close>
definition inc_index_inv1_aux:: "env \<Rightarrow> bool" where
"inc_index_inv1_aux e \<equiv> inc_index_inv1 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

lemma inc_index_invariantRed: "spec inc_index_inv1_aux inc_index (GG inc_index_inv1)"
  unfolding inc_index_inv1_aux_def inc_index_inv1_def dnfp_precondition_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)

definition inc_index_inv2_aux:: "env \<Rightarrow> bool" where
"inc_index_inv2_aux e \<equiv> inc_index_inv2 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"
                                           
lemma inc_index_invariantWhite: "spec inc_index_inv2_aux inc_index (GG inc_index_inv2)"
  unfolding inc_index_inv2_aux_def dnfp_precondition_def inc_index_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def i_Env_def put_def get_state_def put_state_def)
  using le_eq_less_or_eq by fastforce

definition inc_index_inv3_aux:: "env \<Rightarrow> bool" where
"inc_index_inv3_aux e \<equiv> inc_index_inv3 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

lemma inc_index_invariantBlue: "spec inc_index_inv3_aux inc_index (GG inc_index_inv3)"
  unfolding inc_index_inv3_aux_def inc_index_inv3_def dnfp_precondition_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)

definition inc_index_inv :: "env \<Rightarrow> bool" where
"inc_index_inv s \<equiv> (inc_index_inv3 s \<and> inc_index_inv2 s \<and> inc_index_inv1 s)"

definition inc_index_inv_aux:: "env \<Rightarrow> bool" where
"inc_index_inv_aux e \<equiv> inc_index_inv e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

lemma inc_index_invariants: "spec inc_index_inv_aux inc_index (GG inc_index_inv)"
  unfolding inc_index_inv_aux_def inc_index_inv_def GG_def
  by (smt GG_def case_prod_beta' inc_index_inv1_aux_def inc_index_inv2_aux_def inc_index_inv3_aux_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite spec_def)

subsection\<open>Loop update action\<close>

lemma loop_update_action_spec: "spec (loop_update_action_pre_aux e) loop_update_action (GG (loop_update_action_post e))"
  unfolding loop_update_action_pre_aux_def GG_def loop_update_action_post_def loop_update_action_pre_def dnfp_precondition_def dnfp_post_def
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
    apply (simp add: spec_def put_def put_state_def swap_def get_state_def high_Env_def)
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

subsubsection\<open>Invariants - Loop_update_action \<close>

definition loop_update_action_inv1_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv1_aux e \<equiv> loop_update_action_inv1 e \<and> loop_update_action_pre e"

definition loop_update_action_inv2_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv2_aux e \<equiv> loop_update_action_inv2 e \<and> loop_update_action_pre e"

definition loop_update_action_inv3_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv3_aux e \<equiv> loop_update_action_inv3 e \<and> loop_update_action_pre e"
                                                             
lemma loop_update_action_invariantRed: "spec loop_update_action_inv1_aux loop_update_action (GG loop_update_action_inv1)"
   unfolding loop_update_action_inv1_aux_def loop_update_action_inv1_def dnfp_precondition_def  loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
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

lemma loop_update_action_invariantWhite: "spec loop_update_action_inv2_aux loop_update_action (GG loop_update_action_inv2)"
   unfolding loop_update_action_inv2_aux_def GG_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule; simp)
    apply (smt GG_def case_prodD case_prodI2 inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_inv2_def spec_def)
    apply (smt GG_def One_nat_def dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_invariantWhite loop_update_action_inv2_def spec_def split_beta')
   by (smt GG_def One_nat_def Suc_less_eq inc_index_inv2_aux_def inc_index_inv2_def inc_index_invariantWhite less_Suc_eq loop_update_action_inv2_def spec_def split_beta')
   

lemma loop_update_action_invariantBlue: "spec loop_update_action_inv3_aux loop_update_action (GG loop_update_action_inv3)"
   unfolding loop_update_action_inv3_aux_def GG_def 
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule;simp)
     apply (smt GG_def case_prodD case_prodI2 inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue less_numeral_extra(1) loop_update_action_inv3_def spec_def)
    apply (smt GG_def One_nat_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue loop_update_action_inv3_def spec_def split_beta')
   by (smt GG_def One_nat_def Suc_less_eq inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue less_Suc_eq loop_update_action_inv3_def spec_def split_beta')

definition loop_update_action_inv :: "env \<Rightarrow> bool" where
"loop_update_action_inv s \<equiv> (loop_update_action_inv3 s \<and> loop_update_action_inv2 s \<and> loop_update_action_inv1 s)"

definition loop_update_action_inv_aux :: "env \<Rightarrow> bool" where
"loop_update_action_inv_aux s \<equiv> (loop_update_action_inv s \<and> loop_update_action_pre s)"

lemma loop_update_action_invariants: "spec loop_update_action_inv_aux loop_update_action (GG loop_update_action_inv)"
  unfolding loop_update_action_inv_aux_def GG_def loop_update_action_inv_def
  by (smt GG_def case_prodD case_prodI2 loop_update_action_inv1_aux_def loop_update_action_inv2_aux_def loop_update_action_inv3_aux_def loop_update_action_invariantBlue loop_update_action_invariantRed loop_update_action_invariantWhite spec_def)

end