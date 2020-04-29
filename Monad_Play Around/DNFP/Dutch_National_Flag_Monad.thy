theory Dutch_National_Flag_Monad
imports 
  "Dutch_National_Flag_Monad_Definitions_Lemmas"
  "HOL-Library.LaTeXsugar"
begin

section\<open>DNFP\<close>
text\<open>A version using a state-monad for storing the array and the intermediate variable.
This function takes a parameter that defines the size of the unsorted array (the difference between high and i).
This makes the recursion well-defined and will ensure termination since loop-update-action decreases the difference for every single call\<close>
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

subsection\<open>DNFP - Invariants proof\<close>
lemma dnfp_invariantRed: "spec (dnfp_inv1) (dnfp_mon n) (GG dnfp_inv1)"
  unfolding dnfp_inv1_def GG_def 
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_variables_invariants e \<and> low_invariant_is_0_Env e)"])
  apply(intro cond_rule)
  apply (smt GG_def Pair_inject dnfp_inv1_def inc_lowbound_inv1_def inc_lowbound_invariantRed less_numeral_extra(1) loop_update_action_inv1_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dec_highbound_inv1_def dec_highbound_invariantRed dnfp_inv1_def loop_update_action_inv1_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dnfp_inv1_def inc_index_inv1_def inc_index_invariantRed less_one loop_update_action_inv1_def loop_update_action_pre_def spec_def split_beta')
  apply blast
  by(simp add: spec_def skip_def)

lemma dnfp_invariantWhite: "spec dnfp_inv2 (dnfp_mon n) (GG dnfp_inv2)"
  unfolding dnfp_inv2_def  GG_def
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_variables_invariants e \<and> invariant_low_to_j_is_1_Env e)"])
  apply(intro cond_rule; simp)
  apply (smt GG_def dnfp_inv2_def inc_lowbound_inv2_def inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_inv2_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def dec_highbound_inv2_def dec_highbound_invariantWhite dnfp_inv2_def loop_update_action_inv2_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def dnfp_inv2_def inc_index_inv2_def inc_index_invariantWhite loop_update_action_inv2_def loop_update_action_pre_def not_less_eq spec_def split_beta')
  apply blast
  by(simp add: spec_def skip_def)

lemma dnfp_invariantBlue: "spec dnfp_inv3 (dnfp_mon n) (GG dnfp_inv3)"
  unfolding dnfp_inv3_def GG_def
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_variables_invariants e \<and> high_invariant_is_2_Env e)"])
  apply (intro cond_rule; simp)
  apply (smt GG_def dnfp_inv3_def inc_lowbound_inv3_def inc_lowbound_invariantBlue less_numeral_extra(1) loop_update_action_inv3_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def dec_highbound_inv3_def dec_highbound_invariantBlue dnfp_inv3_def loop_update_action_inv3_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def dnfp_inv3_def inc_index_inv3_def inc_index_invariantBlue loop_update_action_inv3_def loop_update_action_pre_def not_less_eq spec_def split_beta')
  apply blast
  by(simp add: spec_def skip_def)

text\<open>All invariants are preserved by the dnfp-function\<close>
lemma dnfp_mon_invariants: "spec (dnfp_inv) (dnfp_mon n) (GG dnfp_inv)"
  by (smt GG_def dnfp_invariantBlue dnfp_invariantRed dnfp_invariantWhite dnfp_inv_def spec_def split_def)

section\<open>Main proof\<close>

text\<open>The invariants and i = high means that the the entire array will be sorted\<close>
lemma dnfp_mon_isSorted: "dnfp_post_final_spec e \<Longrightarrow> sorted (xs e)" 
  unfolding dnfp_post_final_spec_def dnfp_inv_def
  by (smt Suc_1 Suc_leD dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def less_numeral_extra(1) less_or_eq_imp_le less_trans low_invariant_is_0_Env_def not_less sorted_iff_nth_mono_less)

text\<open>DNFP mon preserves the invariants on the ranges and the bounds of the variables\<close>
lemma dnfp_mon_main: "spec (dnfp_mon_spec) (dnfp_mon n) (GG dnfp_mon_spec)"
  unfolding GG_def dnfp_mon_spec_def
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_variables_invariants e \<and> dnfp_inv e)"])
  apply(intro cond_rule)
  apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv_def inc_lowbound_inv1_def inc_lowbound_inv2_def inc_lowbound_inv3_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dec_highbound_inv1_def dec_highbound_inv2_def dec_highbound_inv3_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite dnfp_inv1_def dnfp_inv_def loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv_def inc_index_inv1_def inc_index_inv2_def inc_index_inv3_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite less_one loop_update_action_inv1_def loop_update_action_inv2_def loop_update_action_inv3_def loop_update_action_pre_def spec_def split_beta')
  apply blast
  by(simp add: spec_def skip_def)

text\<open>This lemma is used to established that high and i will be equal if the variables are initiated with the right value (defined by the invariant on the environment)\<close>
lemma aux1: "(spec (\<lambda>e. dnfp_variables_invariants e \<and> n = high e - i e) (dnfp_mon n)
                (\<lambda>x e. high e = i e)) \<Longrightarrow>
           spec
            (\<lambda>xa. ((dnfp_variables_invariants xa \<and> Suc n = high xa - i xa) \<and>
                   (high x, i x) = (high xa, i xa)) \<and>
                  i x < high x)
            (loop_update_action \<bind> (\<lambda>_. dnfp_mon n)) (\<lambda>x e. high e = i e)"
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_variables_invariants e
                                \<and> n = high e - i e)"])
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. Suc n = high e - i e \<and> high e > i e \<and> dnfp_variables_invariants e)"])
  apply(simp add: spec_def swap_def xs_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. n = high e - i e \<and> dnfp_variables_invariants e \<and> i e > low e)"])
  apply(simp add: spec_def i_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def low_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply(simp add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. n = high e - i e \<and> dnfp_variables_invariants e)"])
  apply(simp add: spec_def high_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply linarith
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def swap_def xs_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def i_Env_def put_def get_state_def put_state_def dnfp_variables_invariants_def)
  apply linarith
  by blast

subsection\<open>Main proofs\<close>

text\<open>If dnfp is called with a proper environment and n is the difference between high and i. When High and I will be equal after the termination of the function.
This can be used the termination. And this proof can together with the dnfp-mon main-proof be used to proof that the array will be sorted by the dnfp-function\<close>
lemma dnfp_mon_termination: "spec (dnfp_mon_pre n) (dnfp_mon n) (GG (i_high_equal n))"
  unfolding GG_def dnfp_mon_pre_def dnfp_mon_spec_def i_high_equal_def
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def dnfp_variables_invariants_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  using aux1 apply blast
  by(simp add: spec_def skip_def dnfp_variables_invariants_def)

text\<open>The array will be sorted after the termination of the dnfp function\<close>
lemma dnfp_mon_main_list_sorted: "spec (dnfp_mon_spec_aux n) (dnfp_mon n) (GG array_sorted)"
  unfolding GG_def dnfp_mon_spec_aux_def array_sorted_def
  apply(induction n rule: dnfp_mon.induct)
  apply (simp add: spec_def skip_def dnfp_mon_isSorted dnfp_mon_spec_def dnfp_post_final_spec_def dnfp_variables_invariants_def)
  by (smt GG_def dnfp_mon_invariants dnfp_mon_isSorted dnfp_mon_termination dnfp_mon_pre_def dnfp_mon_spec_def dnfp_post_final_spec_def i_high_equal_def spec_def split_beta')

section\<open>Examples of DNFP\<close>
definition init_env:: "nat array \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

text\<open>A proof to show that the init-env will satisfy the invariant of the environment\<close>
lemma "e = (init_env x) \<and> set(x) \<subseteq> {0,1,2} \<Longrightarrow> dnfp_variables_invariants e"
  unfolding init_env_def dnfp_variables_invariants_def
  by simp

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0])))))\<close>

end