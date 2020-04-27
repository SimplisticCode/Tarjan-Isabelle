theory Dutch_National_Flag_Monad
imports 
  "Dutch_National_Flag_Monad_Definitions_Lemmas"
begin

section\<open>DNFP\<close>
text\<open>A version using a state monad for storing the array and the intermediate variable.
This function takes a parameter that defines the size of the unsorted array (the difference between high and i).
This makes the recursion well-defined and will ensure termination since loop_update_action decreases the difference for every single call\<close>
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

section\<open>DNFP proof\<close>
subsection\<open>DNFP preserves the Invariants proof\<close>
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

text\<open>All invariants are preserved\<close>
lemma dnfp_mon_invariants: "spec (dnfp_mon_inv) (dnfp_mon n) (GG dnfp_mon_inv)"
  by (smt GG_def dnfp_invariantBlue dnfp_invariantRed dnfp_invariantWhite dnfp_mon_inv_def invariants_Env_def spec_def split_def)

section\<open>Main proof\<close>

text\<open>If the invariants are kept and i = high, when the entire array will be sorted\<close>
lemma dnfp_mon_isSorted: "dnfp_post_final_spec e \<Longrightarrow> sorted (xs e)" 
  unfolding dnfp_post_final_spec_def dnfp_mon_inv_def
  by (smt Suc_1 Suc_leD dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def less_numeral_extra(1) less_or_eq_imp_le less_trans low_invariant_is_0_Env_def not_less sorted_iff_nth_mono_less)

text\<open>DNFP mon preserves the invariants on the ranges and the bounds of the variables\<close>
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
   apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> dnfp_mon_inv e)"])
    apply(intro cond_rule)
      apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite less_numeral_extra(1) loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def Pair_inject dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def dnfp_mon_inv_def inc_index_inv1_aux_def inc_index_inv1_def inc_index_inv2_aux_def inc_index_inv2_def inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite less_one loop_update_action_pre_def spec_def split_beta') 
  apply blast
  by(simp add: spec_def skip_def)

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

subsection\<open>Main proofs\<close>
definition dnfp_mon_pre::"nat \<Rightarrow> env \<Rightarrow> bool"  where
"dnfp_mon_pre n e \<equiv> dnfp_precondition e \<and> n = high e - i e"

definition i_high_equal::"nat \<Rightarrow> env \<Rightarrow> bool"  where
 "i_high_equal n e \<equiv> high e = i e"

text\<open>If dnfp is called with a proper environment and n is the difference between high and i. When High and I will be equal after the termination of the function.
This can be used the termination. And this proof can together with the dnfp_mon_main-proof be used to proof that the array will be sorted by the dnfp-function\<close>
lemma dnfp_mon_termination: "spec (dnfp_mon_pre n) (dnfp_mon n) (GG (i_high_equal n))"
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

definition array_sorted where
"array_sorted e \<equiv> sorted(xs e)"

lemma dnfp_mon_main_list_sorted: "spec (dnfp_mon_spec_aux n) (dnfp_mon n) (GG array_sorted)"
  unfolding GG_def dnfp_mon_spec_aux_def array_sorted_def
  apply(induction n rule: dnfp_mon.induct)
  apply (simp add: spec_def skip_def dnfp_mon_isSorted dnfp_mon_spec_def dnfp_post_final_spec_def dnfp_precondition_def)
  by (smt GG_def dnfp_mon_invariants dnfp_mon_isSorted dnfp_mon_termination dnfp_mon_pre_def dnfp_mon_spec_def dnfp_post_final_spec_def i_high_equal_def spec_def split_beta')

section\<open>Examples of DNFP\<close>
definition init_env:: "nat array \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0])))))\<close>

end