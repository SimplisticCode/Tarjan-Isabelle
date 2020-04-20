theory Dutch_National_Flag_Monad_Definitions_Lemmas
imports 
  "Dutch_National_Flag_Monad_Definitions"
begin

  
lemma inc_lowbound_spec: "spec (inc_lowbound_pre e) inc_lowbound (GG (inc_lowbound_post e))"
  unfolding inc_lowbound_pre_def loop_update_action_pre_def GG_def inc_lowbound_post_def loop_update_action_post_def
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
   apply (intro seq_rule[of _ _ "(\<lambda>_ y. i y < high y \<and> i y = i e \<and> high y = high e)"])
    apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
   apply (intro seq_rule[of _ _ "(\<lambda>_ y. high y - i y < high e - i e)"])
    apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
    apply (linarith)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
   apply(simp add: spec_def put_def get_state_def put_state_def low_Env_def)
   apply (intro seq_rule[of _ _ "(\<lambda>x y. i e = i y)"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def i_Env_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
   apply (intro seq_rule[of _ _ "(\<lambda>x y. i e < i y)"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def i_Env_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  by(simp add: spec_def put_def get_state_def put_state_def low_Env_def)

subsubsection\<open>Invariants\<close>
lemma inc_lowbound_invariantRed: "spec inc_lowbound_inv1 inc_lowbound (GG low_invariant_is_0_Env)"
  unfolding inc_lowbound_inv1_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. xs e ! low e = 0 \<and>  (\<forall>x<low e. xs e ! x = 0))"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. xs e ! low e = 0 \<and> (\<forall>x<low e. xs e ! x = 0))"])
   apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
   apply (simp add: spec_def put_def put_state_def get_state_def low_Env_def)
  using less_antisym by blast

lemma inc_lowbound_invariantWhite: "spec inc_lowbound_inv2  inc_lowbound (GG invariant_low_to_j_is_1_Env)"
  unfolding inc_lowbound_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
   apply (simp add: spec_def put_def put_state_def  get_state_def xs_Env_def swap_def get_def i_Env_def low_Env_def return_def)
   apply(intro allI)
  by (simp add: nth_list_update)

lemma inc_lowbound_invariantBlue: "spec inc_lowbound_inv3  inc_lowbound (GG high_invariant_is_2_Env)"
  unfolding inc_lowbound_inv3_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def
  apply(simp_all add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x. x \<ge> high e \<and> x < length (xs e) \<longrightarrow> xs e ! x = 2)"])
  apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x. x \<ge> high e \<and> x < length (xs e) \<longrightarrow> xs e ! x = 2)"])
  apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  by (simp add: spec_def put_def put_state_def get_state_def low_Env_def)

definition inc_lowbound_inv :: "env \<Rightarrow> bool" where
"inc_lowbound_inv s \<equiv> (inc_lowbound_inv3 s \<and> inc_lowbound_inv2 s \<and> inc_lowbound_inv1 s)"

lemma inc_lowbound_invariants: "spec inc_lowbound_inv  inc_lowbound (GG invariants_Env)"
  by (metis (mono_tags, lifting) GG_def inc_lowbound_inv_def  inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite invariants_Env_def spec_def split_def)

subsection\<open>Dec_highbound Invariants\<close>                                          
lemma dec_highbound_spec: "spec (dec_highbound_pre e) dec_highbound (GG (dec_highbound_post e))"
  unfolding dec_highbound_pre_def loop_update_action_pre_def GG_def dec_highbound_post_def loop_update_action_post_def
  apply(simp_all add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
   apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < length (xs e))"])
        apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
           apply(linarith)
           apply(intro allI; simp)
           apply(intro get_rule; intro allI; simp)
           apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
           apply (intro seq_rule[of _ _ "(\<lambda>_ y. (xs e)!(i e) = 2 \<and> (high e = Suc (high y)))"])
           apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
           apply(intro allI; simp)
           apply(intro get_rule; intro allI; simp)
           apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
          apply(intro seq_rule[of _ _ "(\<lambda>_ y.(xs e)!(i e) = 2 \<and> low e = low y)"])
           apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
           apply(intro allI; simp)
          apply(intro get_rule; intro allI; simp)
             apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
        apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e = i y \<and> i e < high e \<and> high e \<le> length (xs e))"])
             apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
           apply(intro allI; simp)
         apply(intro get_rule; intro allI; simp)
        apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
       apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e < high e \<and> high y + 1 = high e \<and> xs e ! i e = 2 \<and> xs e = xs y \<and> i e = i y \<and> high e \<le> length (xs e))"])         
       apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
        apply(intro allI; simp)
       apply(intro get_rule; intro allI; simp)
       apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
         apply(intro allI)
       apply auto[1]
      apply(intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
      apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
       apply(intro allI; simp)
       apply(intro get_rule; intro allI; simp)
       apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
      apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < high e)"])
      apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
       apply(intro allI; simp)
      apply(intro get_rule; intro allI; simp)
      apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
     apply(intro seq_rule[of _ _ "(\<lambda>_ y. high y < high e \<and> low e = low y)"])
      apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
       apply(intro allI; simp)
      apply(intro get_rule; intro allI; simp)
      apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
     apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e = i y \<and> high y < high e)"])
      apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
       apply(intro allI; simp)
      apply(intro get_rule; intro allI; simp)
      apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
     apply(intro seq_rule[of _ _ "(\<lambda>_ y. i e = i y \<and> i e < high e \<and> high y < high e)"])
      apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def)
       apply(intro allI; simp)
   apply(intro get_rule; intro allI; simp)
   apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def)
   apply(intro allI)
  by(linarith)

subsubsection\<open>Invariants\<close>
lemma dec_highbound_invariantRed: "spec dec_highbound_inv1 dec_highbound (GG low_invariant_is_0_Env)"
    unfolding dec_highbound_inv1_def loop_update_action_pre_def GG_def low_invariant_is_0_Env_def
    apply(simp_all add: dec_highbound_def)
    apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>_ e. (\<forall>x < low e. xs e ! x = 0) \<and> low e \<le> i e \<and> high e \<ge> i e \<and> length (xs e) > high e)"])
     apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply(linarith)
     apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
    by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)

lemma dec_highbound_invariantWhite: "spec dec_highbound_inv2 dec_highbound (GG invariant_low_to_j_is_1_Env)"
    unfolding dec_highbound_inv2_def loop_update_action_pre_def GG_def invariant_low_to_j_is_1_Env_def
    apply(simp_all add: dec_highbound_def)
        apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>x e. low e \<le> i e \<and> high e \<ge> i e \<and> length (xs e) > high e \<and> (\<forall>x. low e \<le> x \<and> x < i e \<longrightarrow> xs e ! x = Suc 0))"])
     apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply linarith
     apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
    by (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)

lemma dec_highbound_invariantBlue: "spec dec_highbound_inv3 dec_highbound (GG high_invariant_is_2_Env)"
    unfolding dec_highbound_inv3_def loop_update_action_pre_def GG_def high_invariant_is_2_Env_def
    apply(simp_all add: dec_highbound_def)
    apply(intro get_rule; intro allI; simp)
     apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def xs_Env_def swap_def get_def return_def)
    apply(intro allI)
    by (smt Suc_leI Suc_pred diff_is_0_eq' leD le_eq_less_or_eq length_list_update less_imp_diff_less nth_list_update nth_list_update_neq)

definition dec_highbound_inv :: "env \<Rightarrow> bool" where
"dec_highbound_inv s \<equiv> (dec_highbound_inv3 s \<and> dec_highbound_inv2 s \<and> dec_highbound_inv1 s)"

lemma dec_highbound_invariants: "spec dec_highbound_inv dec_highbound (GG invariants_Env)"
  by (metis (mono_tags, lifting) GG_def dec_highbound_inv_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite invariants_Env_def spec_def split_def)

subsection\<open>Inc_index Invariants\<close>
lemma inc_index_spec: "spec (inc_index_pre e) inc_index (GG (inc_index_post e))"
  unfolding inc_index_pre_def loop_update_action_pre_def GG_def inc_index_post_def loop_update_action_post_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI;simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def i_Env_def)
  by linarith

subsubsection\<open>Invariants\<close>
lemma inc_index_invariantRed: "spec inc_index_inv1 inc_index (GG low_invariant_is_0_Env)"
  unfolding inc_index_inv1_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)

lemma inc_index_invariantWhite: "spec inc_index_inv2 inc_index (GG invariant_low_to_j_is_1_Env)"
  unfolding inc_index_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def i_Env_def put_def get_state_def put_state_def)
  using less_SucE by blast

lemma inc_index_invariantBlue: "spec inc_index_inv3 inc_index (GG high_invariant_is_2_Env)"
  unfolding inc_index_inv3_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def
  apply(simp_all add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def i_Env_def put_def get_state_def put_state_def)

definition inc_index_inv :: "env \<Rightarrow> bool" where
"inc_index_inv s \<equiv> (inc_index_inv3 s \<and> inc_index_inv2 s \<and> inc_index_inv1 s)"

lemma inc_index_invariants: "spec inc_index_inv inc_index (GG invariants_Env)"
  by (metis (mono_tags, lifting) GG_def inc_index_inv_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite invariants_Env_def spec_def split_def)

end