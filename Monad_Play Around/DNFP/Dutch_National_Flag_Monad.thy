theory Dutch_National_Flag_Monad
imports 
  "Dutch_National_Flag_Monad_Definitions_Lemmas"
begin

section\<open>DNFP\<close>
text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
fun dnfp_mon:: "nat \<Rightarrow> (env, unit) state" where
  case0:"dnfp_mon 0  = skip"|
  caseN:"dnfp_mon (Suc n) = do {
                        (h, j) \<leftarrow> get (\<lambda>e. (high e, i e));
                        (if h > j then do{
                          loop_update_action;
                          dnfp_mon n
                         }
                       else skip
                      )}"

section\<open>Lemmas\<close>
subsection\<open>Hoare proofs\<close>
subsection\<open>DNFP_Mon Auxillary lemmas\<close>
lemma dnfp_aux1: "spec (\<lambda>y. length (xs e) = length (xs y)) (dnfp_mon v) (\<lambda>x y. length (xs e) = length (xs y))"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux2: "spec (\<lambda>y. high y \<le> high e) (dnfp_mon v) (\<lambda>x y. high y \<le> high e)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux3: "spec (\<lambda>y. low e \<le> low y) (dnfp_mon v) (\<lambda>x y. low e \<le> low y)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux4: "spec (\<lambda>y. i e \<le> i y) (dnfp_mon v) (\<lambda>x y. i e \<le> i y)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def)
  by (simp add: skip_def)

lemma dnfp_aux5: "spec (\<lambda>y. high y - i y \<le> high e - i e) (dnfp_mon v) (\<lambda>x y. high y - i y \<le> high e - i e)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
   apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply blast
  apply(simp add: spec_def)
  by (simp add: skip_def)

lemma dnfp_aux6: "spec (\<lambda>y. mset (xs e) = mset (xs y)) (dnfp_mon v) (\<lambda>x y. mset (xs e) = mset (xs y))"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply blast
  apply(simp add: spec_def)
  by (simp add: skip_def)

subsection\<open>DNFP proof\<close>
lemma dnfp_prepost: "spec (dnfp_pre n e) (dnfp_mon n) (GG (dnfp_post e))"
  apply(induction rule: dnfp_mon.induct)
  unfolding dnfp_pre_def dnfp_pre_aux_def GG_def dnfp_post_def
    apply(simp add: spec_def)
   apply (simp add: skip_def)
  apply(intro conj_rule_right; simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
   apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
        apply(intro allI; simp)
  using dnfp_aux1 apply blast
        apply(simp add: spec_def skip_def)
   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
       apply(intro allI; simp)
  using dnfp_aux2 apply blast
    apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  using dnfp_aux3 apply blast
  apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  using dnfp_aux4 apply blast
  apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)             
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
       apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
         apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply linarith
    apply(intro allI; simp)
  using dnfp_aux5 apply blast
  apply(simp add: spec_def skip_def)

 apply(intro get_rule; intro allI; clarify)
 apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
            apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
   apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
    apply(intro allI; simp)
  using dnfp_aux6 apply blast
  by(simp add: spec_def skip_def)

subsection\<open>Invariants proof\<close>
lemma dnfp_invariantRed: "spec (dnfp_inv1) (dnfp_mon n) (GG dnfp_inv1)"
  unfolding dnfp_inv1_def dnfp_pre_aux_def GG_def 
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
   apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> low_invariant_is_0_Env e)"])
    apply(intro cond_rule)
  apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_invariantRed lessI loop_update_action_pre_def prod.simps(1) spec_def)
  apply (smt GG_def case_prodD case_prodI2 dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_invariantRed loop_update_action_pre_def prod.simps(1) spec_def)
    apply (smt GG_def case_prodD case_prodI2 inc_index_inv1_aux_def inc_index_inv1_def inc_index_invariantRed less_one loop_update_action_pre_def prod.simps(1) spec_def) 
   apply blast
    apply(simp add: spec_def)
   by(simp add: skip_def)

lemma dnfp_invariantWhite: "spec dnfp_inv2 (dnfp_mon n) (GG dnfp_inv2)"
  unfolding dnfp_inv2_def  GG_def dnfp_pre_aux_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> invariant_low_to_j_is_1_Env e)"])
    apply(intro cond_rule; simp)
      apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_invariantWhite lessI loop_update_action_pre_def spec_def)
     apply (smt GG_def One_nat_def case_prodD case_prodI2 dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_invariantWhite loop_update_action_pre_def spec_def)
  apply (smt GG_def One_nat_def Suc_less_eq inc_index_inv2_aux_def inc_index_inv2_def inc_index_invariantWhite less_Suc_eq loop_update_action_pre_def spec_def split_beta')
  apply blast
    apply(simp add: spec_def)
   by(simp add: skip_def)

lemma dnfp_invariantBlue: "spec dnfp_inv3 (dnfp_mon n) (GG dnfp_inv3)"
  unfolding dnfp_inv3_def dnfp_pre_aux_def  GG_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> high_invariant_is_2_Env e)"])
    apply (intro cond_rule; simp)
      apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue lessI loop_update_action_pre_def spec_def)
     apply (smt GG_def One_nat_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def Suc_less_eq inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue less_Suc_eq loop_update_action_pre_def spec_def split_beta')
 apply blast
     apply(simp add: spec_def)
  by(simp add: skip_def)

section\<open>Main proof\<close>
definition dnfp_mon_inv :: "env \<Rightarrow> bool" where
"dnfp_mon_inv e \<equiv> ((dnfp_inv3 e) \<and> (dnfp_inv2 e) \<and> (dnfp_inv1 e))"

lemma dnfp_mon_invariants: "spec (dnfp_mon_inv) (dnfp_mon n) (GG dnfp_mon_inv)"
  by (smt GG_def dnfp_invariantBlue dnfp_invariantRed dnfp_invariantWhite dnfp_mon_inv_def invariants_Env_def spec_def split_def)

definition dnfp_post_spec where
"dnfp_post_spec e \<equiv> dnfp_mon_inv e \<and> i e = high e"

lemma dnfp_mon_isSorted: "dnfp_post_spec e \<Longrightarrow> sorted (xs e)" 
  unfolding  dnfp_post_spec_def dnfp_mon_inv_def
  by (smt Suc_1 Suc_leD dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def less_numeral_extra(1) less_or_eq_imp_le less_trans low_invariant_is_0_Env_def not_less sorted_iff_nth_mono_less)

definition dnfp_post_spec1 where
"dnfp_post_spec1 e \<equiv> dnfp_mon_inv e \<and> i e = high e \<and> sorted(xs e)"

definition range_0:: "env \<Rightarrow> nat array" where
"range_0 e \<equiv> nths (xs e) (set(upt 0 (low e)))"

definition range_1:: "env \<Rightarrow> nat array" where
"range_1 e \<equiv> nths (xs e) (set(upt (low e) (i e)))"

definition range_2:: "env \<Rightarrow> nat array" where
"range_2 e \<equiv> nths (xs e) (set(upt (high e) (length (xs e))))"

lemma as: "nths x {0..<z} = take z x"
  by (simp add: atLeast0LessThan)

(*I don't get why I can't prove this*)
lemma as1: "\<lbrakk>n = length x; z < n\<rbrakk> \<Longrightarrow> nths x {0..<z} @ nths x {z..<n}= take n x"
  apply(induction n arbitrary: x)
   apply simp
  sorry

lemma complete_range_aux: "\<lbrakk>n = length x; z < length x\<rbrakk> \<Longrightarrow> nths x {0..<z} @ nths x {z..<n} = x"
  apply(induction n arbitrary: z)
   apply simp
  by (simp add: as1)


lemma complete_range: "\<lbrakk>z \<le> y; n = length x; y < length x\<rbrakk> \<Longrightarrow> nths x {0..<z} @ nths x {z..<y} @ nths x {y..<n} = x"
  apply(induction n arbitrary: z y x)
   apply simp
  sorry

lemma range_isComplete: "\<lbrakk>dnfp_precondition e; high e = i e\<rbrakk> \<Longrightarrow> concat[range_0 e, range_1 e,  range_2 e] = xs e"
  unfolding range_0_def range_1_def range_2_def dnfp_precondition_def
  apply(auto)
  by (metis append.simps(1) append_Nil2 atLeastLessThan0 atLeastLessThan_empty_iff complete_range le0 le_SucE le_neq_implies_less le_numeral_extra(3) le_zero_eq length_0_conv less_Suc_eq_0_disj nths_empty same_append_eq set_upt zero_induct)

definition sorted_range_get:: "env \<Rightarrow> nat array" where
"sorted_range_get e \<equiv> range_0 e @ range_1 e @ range_2 e"

definition sorted_range:: "env \<Rightarrow> bool" where
"sorted_range e \<equiv> sorted(sorted_range_get e)"

lemma range_0_isZero: "low_invariant_is_0_Env e \<Longrightarrow> \<forall>x \<in> set(range_0 e). x = 0"
  unfolding low_invariant_is_0_Env_def range_0_def
  by (smt atLeast_upt lessThan_iff mem_Collect_eq set_nths)

lemma range_0_sorted: "dnfp_mon_inv e \<Longrightarrow> sorted (range_0 e)"
  unfolding dnfp_mon_inv_def dnfp_inv3_def dnfp_inv2_def dnfp_inv1_def range_1_def dnfp_precondition_def
  by (metis eq_iff less_trans nth_mem range_0_isZero sorted_iff_nth_mono_less)

lemma range_1_isOne: "invariant_low_to_j_is_1_Env e \<Longrightarrow> \<forall>x \<in> set(range_1 e). x = 1"
  unfolding invariant_low_to_j_is_1_Env_def range_1_def
  by (smt atLeastLessThan_iff mem_Collect_eq set_nths set_upt)

lemma range_1_sorted: "dnfp_mon_inv e \<Longrightarrow> sorted (range_1 e)"
  by (smt diff_is_0_eq dnfp_inv2_def dnfp_mon_inv_def le_neq_implies_less length_take less_trans min.absorb2 nat_le_linear not_one_less_zero nth_mem range_1_def range_1_isOne sorted01 sorted_iff_nth_mono take_all)

lemma ranges_sorted: "\<lbrakk>invariant_low_to_j_is_1_Env e; low_invariant_is_0_Env e\<rbrakk> \<Longrightarrow> sorted(range_0 e @ range_1 e)"
  by (metis less_trans nat_le_linear not_one_le_zero nth_mem range_0_isZero range_1_isOne sorted_append sorted_iff_nth_mono_less)

lemma range_2_isTwo: "high_invariant_is_2_Env e \<Longrightarrow> \<forall>x \<in> set(range_2 e). x = 2"
  unfolding high_invariant_is_2_Env_def range_2_def
  by (smt atLeastLessThan_iff mem_Collect_eq set_nths set_upt)

lemma range_2_sorted: "dnfp_mon_inv e \<Longrightarrow> sorted (range_2 e)"
  by (metis dnfp_inv3_def dnfp_mon_inv_def eq_iff less_trans nth_mem range_2_isTwo sorted_sorted_wrt sorted_wrt_iff_nth_less)

lemma "dnfp_mon_inv e \<Longrightarrow> sorted(sorted_range_get e)"
  by (metis Suc_1 dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def lessI less_imp_le_nat range_0_isZero range_0_sorted range_1_isOne range_1_sorted range_2_isTwo range_2_sorted sorted_append sorted_range_get_def zero_le)

lemma sorted_aux: "dnfp_mon_inv e \<Longrightarrow> sorted_range e"
  unfolding sorted_range_def
  by (metis Suc_1 dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def lessI less_imp_le_nat range_0_isZero range_0_sorted range_1_isOne range_1_sorted range_2_isTwo range_2_sorted sorted_append sorted_range_get_def zero_le)

lemma "sorted_range e \<and> i e = high e \<and> dnfp_precondition e \<Longrightarrow> sorted (xs e)"
  unfolding sorted_range_def sorted_range_get_def dnfp_precondition_def
  using dnfp_precondition_def range_isComplete by auto

definition dnfp_mon_spec where
"dnfp_mon_spec e \<equiv> dnfp_precondition e
                    \<and> dnfp_mon_inv e
                    \<and> sorted_range e"

lemma dnfp_mon_main: "spec (dnfp_mon_spec) (dnfp_mon n) (GG dnfp_mon_spec)"
  unfolding GG_def dnfp_mon_spec_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
   apply(simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
   apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
   apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> dnfp_mon_inv e \<and> sorted_range e)"])
    apply(intro cond_rule)
      apply(intro conj_rule_right; simp)
  apply (smt GG_def dnfp_inv1_def dnfp_mon_inv_def inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_invariantRed less_numeral_extra(1) loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite less_one loop_update_action_pre_def spec_def split_beta')
  apply (smt Dutch_National_Flag_Monad.sorted_aux GG_def dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_pre_def spec_def split_beta')
      apply(intro conj_rule_right)
        apply (smt GG_def Pair_inject dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_invariantRed dnfp_inv1_def dnfp_mon_inv_def loop_update_action_pre_def spec_def split_beta')
      apply (smt GG_def Pair_inject dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def loop_update_action_pre_def spec_def split_beta')
      apply (smt Dutch_National_Flag_Monad.sorted_aux GG_def Pair_inject dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def loop_update_action_pre_def spec_def split_beta')
      apply(intro conj_rule_right)
        apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_mon_inv_def inc_index_inv1_aux_def inc_index_inv1_def inc_index_invariantRed less_one loop_update_action_pre_def spec_def split_beta')
     apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_index_inv1_aux_def inc_index_inv1_def inc_index_inv2_aux_def inc_index_inv2_def inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite less_one loop_update_action_pre_def spec_def split_beta')
  apply (smt Dutch_National_Flag_Monad.sorted_aux GG_def Pair_inject dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_index_inv1_aux_def inc_index_inv1_def inc_index_inv2_aux_def inc_index_inv2_def inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite less_one loop_update_action_pre_def spec_def split_beta')
  apply blast
  by(simp add: spec_def skip_def)

(*
  add precondition:
  Everything outside n is sorted
  high to n
  And finally everything should be sorted
  Post condition high = i 
*)


definition i_high_equal::"nat \<Rightarrow> env \<Rightarrow> bool"  where
 "i_high_equal n e \<equiv> high e = i e"

definition dnfp_mon_pre::"nat \<Rightarrow> env \<Rightarrow> bool"  where
"dnfp_mon_pre n e \<equiv> dnfp_precondition e \<and> n = high e - i e"

lemma aux1: "(spec (\<lambda>e. dnfp_precondition e \<and> n = high e - i e) (dnfp_mon n)
                (\<lambda>x e. high e = i e)) \<Longrightarrow>
           spec
            (\<lambda>xa. ((dnfp_precondition xa \<and> Suc n = high xa - i xa) \<and>
                   (high x, i x) = (high xa, i xa)) \<and>
                  i x < high x)
            (loop_update_action \<bind> (\<lambda>_. dnfp_mon n)) (\<lambda>x e. high e = i e)"
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e
                                \<and> n = high e - i e)"])
   apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
   apply(intro cond_rule)
     apply(simp add: inc_lowbound_def)
     apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. Suc n = high e - i e \<and> high e > i e \<and> dnfp_precondition e)"])
      apply(simp add: spec_def swap_def xs_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
   apply(intro allI; simp)
      apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. n = high e - i e \<and> dnfp_precondition e \<and> i e > low e)"])
  apply(simp add: spec_def i_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
  apply linarith
   apply(intro allI; simp)
      apply(intro get_rule; intro allI; simp)
       apply(simp add: spec_def low_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
     apply(simp add: dec_highbound_def)
     apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. n = high e - i e \<and> dnfp_precondition e)"])
     apply(simp add: spec_def high_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
  apply linarith
   apply(intro allI; simp)
      apply(intro get_rule; intro allI; simp)
        apply(simp add: spec_def swap_def xs_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
        apply(simp add: inc_index_def)
      apply(intro get_rule; intro allI; simp)
   apply(simp add: spec_def i_Env_def put_def get_state_def put_state_def dnfp_precondition_def)
  apply linarith
  by blast

lemma dnfp_mon_main_aux: "spec (dnfp_mon_pre n) (dnfp_mon n) (GG (i_high_equal n))"
  unfolding GG_def dnfp_mon_pre_def dnfp_mon_spec_def i_high_equal_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
   apply(simp add: skip_def)
  apply (simp add: dnfp_precondition_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  using aux1 apply blast
  by(simp add: spec_def skip_def dnfp_precondition_def)

definition dnfp_mon_spec_aux:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"dnfp_mon_spec_aux n e \<equiv> n = high e - i e \<and> dnfp_mon_spec e"

definition list_sorted where
"list_sorted e \<equiv> sorted(xs e)"

lemma dnfp_mon_main_list_sorted: "spec (dnfp_mon_spec_aux n) (dnfp_mon n) (GG list_sorted)"
  unfolding GG_def dnfp_mon_spec_aux_def  list_sorted_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
   apply(simp add: skip_def)
  apply (simp add: dnfp_mon_isSorted dnfp_mon_spec_def dnfp_post_spec_def dnfp_precondition_def)
  by (smt GG_def dnfp_mon_invariants dnfp_mon_isSorted dnfp_mon_main_aux dnfp_mon_pre_def dnfp_mon_spec_def dnfp_post_spec_def i_high_equal_def spec_def split_beta')

end