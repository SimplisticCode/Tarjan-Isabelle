theory Dutch_National_Flag_Monad
imports 
  "Dutch_National_Flag_Monad_Definitions_Lemmas"
  "HOL-Library.LaTeXsugar"
begin

section\<open>Proof of DNFP\<close>
text\<open>A version using a state-monad for storing the array and the intermediate variable.
This function takes a parameter that defines the size of the unsorted array (the difference between the variables @{text high} and @{text i} due to the invariant on the ranges).
This makes the recursion well-defined and will ensure termination since @{text loop_update_action} decreases the difference for every single call\<close>
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
text\<open>These proofs show that @{text dnfp_mon} preserves the invariants.
   They use the already established lemmas about how the definitions/functions that @{text dnfp_mon} consists of all preserve the invariants of the ranges (red, white and blue).\<close>
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

subsection\<open>Aux. proofs of the DNFP\<close>
text\<open>@{text Dnfp_mon} preserves the invariants on the ranges and the bounds of the variables. This proof is actually not necessary to proof that the method sorts the array\<close>
lemma dnfp_env_inv: "spec (dnfp_mon_spec) (dnfp_mon n) (GG dnfp_mon_spec)"
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

text\<open>This lemma is used to establish that variables @{text high} and @{text i} will be equal if the variables are initiated with the right value (defined by the invariant on the environment @{text dnfp_variables_invariants})\<close>
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
text\<open>If @{text dnfp_mon} is called with a proper environment and the parameter of the function @{text n} is the difference between the variables @{text high} and @{text i}. 
When @{text high} and @{text i} will be equal after the termination of the function.
This lemma can be used the termination. And this proof can together with the dnfp-mon main-proof be used to prove that @{text dnfp_mon} will sort the array \<close>
lemma dnfp_mon_termination: "spec (dnfp_mon_pre n) (dnfp_mon n) (GG (i_high_equal n))"
  unfolding GG_def dnfp_mon_pre_def dnfp_mon_spec_def i_high_equal_def
  apply(induction n rule: dnfp_mon.induct)
  apply(simp add: spec_def skip_def dnfp_variables_invariants_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  using aux1 apply blast
  by(simp add: spec_def skip_def dnfp_variables_invariants_def)

text\<open>The invariants and the fact @{text i} = @{text high} means that the the entire array will be sorted. 
    This lemma makes it possible to show that @{text dnfp_mon} will sort the array\<close>
lemma dnfp_mon_isSorted: "dnfp_post_final_spec e \<Longrightarrow> (array_sorted e)" 
  unfolding dnfp_post_final_spec_def dnfp_inv_def array_sorted_def
  by (smt Suc_1 Suc_leD dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def less_numeral_extra(1) less_or_eq_imp_le less_trans low_invariant_is_0_Env_def not_less sorted_iff_nth_mono_less)

text\<open>The array is sorted after the termination of the dnfp function. 
  This proof depends mainly on two proofs. 
\begin{enumerate}
  \item The variables @{text i} and @{text high} are equal by the termination of @{text dnfp_mon}
  \item @{text Dnfp_mon} preserves the invariant of the ranges.
\end{enumerate}
These two facts are by the proof of lemma @{text dnfp_mon_isSorted} enough to show that the array is sorted in the final state.\<close>
theorem dnfp_mon_main_list_sorted: "spec (dnfp_mon_spec_aux n) (dnfp_mon n) (GG array_sorted)"
  unfolding GG_def dnfp_mon_spec_aux_def
  apply(induction n rule: dnfp_mon.induct)
   apply (simp add: spec_def skip_def  dnfp_mon_spec_def  dnfp_variables_invariants_def)
  using array_sorted_def dnfp_mon_isSorted dnfp_post_final_spec_def le_antisym apply blast
  by (smt GG_def case_prod_beta' dnfp_mon_invariants dnfp_mon_isSorted dnfp_mon_pre_def dnfp_mon_spec_def dnfp_mon_termination dnfp_post_final_spec_def i_high_equal_def spec_def)

section\<open>Examples of DNFP\<close>
text\<open>The definiton of how to set up the state-monad/environment with the right values based on an array.\<close>
definition init_env:: "nat array \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

text\<open>A proof to show that the init-env will satisfy the invariant of the environment\<close>
lemma "e = (init_env x) \<and> set(x) \<subseteq> {0,1,2} \<Longrightarrow> dnfp_variables_invariants e"
  unfolding init_env_def dnfp_variables_invariants_def
  by simp

text\<open>This is just some examples of how to run the algorithm and some concrete assertions\<close>
value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2])))))\<close>
value \<open>assert(sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0])))))\<close>

section\<open>Experiences\<close>
text\<open>A general rule of thumb when carrying out a single proof is to divide the methods as much as possible and limit the number of parameters. By following these rules, it simplifies the proof substantial since it is a lot easier to proof five small methods compared to one big. It is also far easier to reason about small methods.
It is also vital to establish a hierarchy of pre- and post-conditions that can be used in the proof. This hierarchy enables the reuse of lemmas of the simple methods inside the compound methods.\<close>
text\<open>Not all programs work with the current syntax. An example of this is two get-statements in a row inside a method. This syntax is currently not supported by the HOL proof-rules. Instead, the two get-statements should be captured into one get-statement that returns multiple values.
     I also have experienced how methods higher-order functions like @{text nths} from the list library should be avoided, since they have bad proof-support. Instead, quantifiers should be used when working with lists.\<close>

text\<open>I have also learned that if a proof can't be proved by first rewriting and afterward Sledgehammer. It means that either it is unprovable or Isabelle needs some more information to prove it. This information can be given by adding some more lemmas. An example of this is the lemmas that can be seen the section Aux. lemmas about values inside the array.\<close>
end