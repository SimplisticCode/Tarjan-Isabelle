theory Dutch_National_Flag_Monad_Definitions
imports 
  Main
  "../State_Monad_HL"
  "HOL-Library.Multiset"
begin
type_synonym 'a array = "'a list"
  
section\<open>Monad definitions\<close>
record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat array"

subsection\<open>update functions\<close>
definition high_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "high_Env s v = s \<lparr> high := v \<rparr>"
definition low_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "low_Env s v = s \<lparr> low := v \<rparr>"
definition i_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "i_Env s v = s \<lparr> i := v \<rparr>"
definition xs_Env:: "env \<Rightarrow> nat array  \<Rightarrow> env" where "xs_Env s v = s \<lparr> xs := v \<rparr>"

theorem put_high_rule: "spec (\<lambda>x. p () (x \<lparr> high := v \<rparr>)) (put high_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def high_Env_def)

theorem put_low_rule: "spec (\<lambda>x. p () (x \<lparr> low := v \<rparr>)) (put low_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def low_Env_def)

theorem put_i_rule: "spec (\<lambda>x. p () (x \<lparr> i := v \<rparr>)) (put i_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def i_Env_def)

theorem put_xs_rule: "spec (\<lambda>x. p () (x \<lparr> xs := v \<rparr>)) (put xs_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def xs_Env_def)


definition swap:: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array" where
"swap l x y \<equiv> (if x < length l \<and> y < length l then l[x := l!y, y := l!x] else l)"

lemma length_swap: "length(swap l x y) = length l"
  by(simp add: swap_def)

lemma distinct_swap[simp]:
  "distinct(swap l x y) = distinct l"
  by(simp add: swap_def)

lemma mset_swap: "mset (swap l x y) = mset l"
  by (simp add: swap_def mset_swap)

section\<open>DNFP function definitions\<close>
definition inc_lowbound where
"inc_lowbound \<equiv> do{
                  (l, s, j) \<leftarrow> get (\<lambda>e. (low e, xs e, i e));  
                  put xs_Env (swap s j l);
                  j \<leftarrow> get i;                                   
                  put i_Env (Suc j);
                  l \<leftarrow> get low;  
                  put low_Env (Suc l)
                }"

definition dec_highbound where
"dec_highbound \<equiv> do{
                    h \<leftarrow> get high;
                    put high_Env (h - 1);
                    (s, j, h) \<leftarrow> get (\<lambda>e. (xs e, i e, high e));
                    put xs_Env (swap s j h)
                }"

definition inc_index where
"inc_index \<equiv> do{
                  j \<leftarrow> get i;
                  put i_Env (Suc j)
                }"

definition loop_update_action where
"loop_update_action \<equiv> 
  do{
    (s, j) \<leftarrow> get (\<lambda>e. (xs e, i e));
    (if s!j < 1 then do {
      inc_lowbound
    } else (if s!j > 1 then do 
    {
      dec_highbound
    }
   else do {
      inc_index
   }))
  }"


definition init_env:: "nat array \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

definition init_state_env:: "nat array \<Rightarrow> (env, unit) state" where
  "init_state_env l \<equiv> State (\<lambda>x. ((),init_env l))"

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0]))))\<close>

section\<open>Definiton of all the Pre and postconditions\<close>

subsection\<open>The invariants are taken from https://en.wikipedia.org/wiki/Dutch_national_flag_problem\<close>
definition low_invariant_is_0_Env where
"low_invariant_is_0_Env e \<equiv> (\<forall>x. x < (low e) \<longrightarrow> (xs e)!x = 0)"

definition invariant_low_to_j_is_1_Env where
"invariant_low_to_j_is_1_Env e \<equiv> (\<forall>x. (x \<ge> (low e) \<and> x < (i e)) \<longrightarrow> (xs e)!x = 1)"

definition high_invariant_is_2_Env where
"high_invariant_is_2_Env e\<equiv> (\<forall>x. x \<ge> (high e) \<and> x < length (xs e) \<longrightarrow> (xs e)!x = 2)"

definition invariants_Env:: "env \<Rightarrow> bool" where
"invariants_Env e \<equiv> high_invariant_is_2_Env e
              \<and> invariant_low_to_j_is_1_Env e
              \<and> low_invariant_is_0_Env e"

text\<open>This can be used in the other pre and post-conditions for the methods inside loop_update_actions\<close>

subsection\<open>Pre- and Postconditions\<close>

subsubsection\<open>Pre-conditions\<close>
definition dnfp_precondition:: "env \<Rightarrow> bool" where
"dnfp_precondition e \<equiv> high e \<ge> i e
                      \<and> i e \<ge> low e 
                      \<and> length (xs e) \<ge> high e
                      \<and> set (xs e) \<subseteq> {0,1,2}"

definition dnfp_pre_aux:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"dnfp_pre_aux n e \<equiv> 
              dnfp_precondition e
              \<and> high e - i e = n"

definition dnfp_pre:: "nat \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
"dnfp_pre n e s \<equiv> s = e
              \<and> dnfp_pre_aux n e"


definition loop_update_action_pre:: "env \<Rightarrow> bool" where
"loop_update_action_pre e \<equiv> dnfp_precondition e \<and> high e > i e"

definition loop_update_action_pre_aux:: "env \<Rightarrow> env \<Rightarrow> bool" where
"loop_update_action_pre_aux e s \<equiv> s = e
                              \<and> loop_update_action_pre e"

definition loop_update_action_inv1 where 
"loop_update_action_inv1 e \<equiv> dnfp_precondition e 
                            \<and> low_invariant_is_0_Env e"

definition loop_update_action_inv2 where 
"loop_update_action_inv2 e \<equiv> dnfp_precondition e 
                              \<and> invariant_low_to_j_is_1_Env e"

definition loop_update_action_inv3 where 
"loop_update_action_inv3 e \<equiv> dnfp_precondition e 
                              \<and> high_invariant_is_2_Env e"

definition dnfp_post where 
"dnfp_post e e2 \<equiv> length (xs e) = length (xs e2)
                  \<and> high e \<ge> high e2
                  \<and> low e \<le> low e2
                  \<and> i e \<le> i e2
                  \<and> high e - i e \<ge> high e2 - i e2
                  \<and> mset (xs e) = mset (xs e2)"
(*This needs to change a little bit*)

definition loop_update_action_post where
"loop_update_action_post e e' \<equiv> dnfp_post e e'"

definition inc_lowbound_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_pre e s \<equiv> s = e
                        \<and> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1"

definition inc_lowbound_inv1 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv1 s \<equiv> dnfp_precondition s
                        \<and> low_invariant_is_0_Env s"

definition inc_lowbound_inv2 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv2 s \<equiv> dnfp_precondition s
                        \<and> invariant_low_to_j_is_1_Env s"

definition inc_lowbound_inv3 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv3 s \<equiv> dnfp_precondition s
                        \<and> high_invariant_is_2_Env s"

definition dec_highbound_pre where 
"dec_highbound_pre e s\<equiv> e = s
                        \<and> loop_update_action_pre e 
                        \<and> (xs e)!(i e) > 1"

definition dec_highbound_inv1 where 
"dec_highbound_inv1 e \<equiv> dnfp_precondition e 
                        \<and> low_invariant_is_0_Env e"

definition dec_highbound_inv2 where 
"dec_highbound_inv2 e \<equiv> dnfp_precondition e 
                        \<and> invariant_low_to_j_is_1_Env e"

definition dec_highbound_inv3 where 
"dec_highbound_inv3 e \<equiv> dnfp_precondition e 
                        \<and> high_invariant_is_2_Env e"

definition inc_index_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_pre e s \<equiv> e = s 
                      \<and> loop_update_action_pre e
                      \<and> \<not>(xs e)!(i e) > 1
                      \<and> \<not>(xs e)!(i e) < 1"

definition inc_index_inv1:: "env \<Rightarrow> bool" where 
"inc_index_inv1 e \<equiv> dnfp_precondition e
                      \<and> low_invariant_is_0_Env e"

definition inc_index_inv2:: "env \<Rightarrow> bool" where 
"inc_index_inv2 e \<equiv> dnfp_precondition e
                      \<and> invariant_low_to_j_is_1_Env e"

definition inc_index_inv3:: "env \<Rightarrow> bool" where
"inc_index_inv3 e \<equiv> dnfp_precondition e
                    \<and> high_invariant_is_2_Env e"

subsubsection\<open>Post-conditions\<close>
definition inc_lowbound_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_post e e'\<equiv> high e = high e'
                          \<and> low e < low e'
                          \<and> loop_update_action_post e e'
                          \<and> i e < i e'"

definition dec_highbound_post where 
"dec_highbound_post e e' \<equiv> length (xs e') > high e' 
                              \<and> high e > high e' 
                              \<and> low e = low e'
                              \<and> i e = i e'
                              \<and> (xs e')!(high e') = 2
                              \<and> loop_update_action_post e e'"

definition inc_index_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_post e e' \<equiv> high e = high e' 
                      \<and> low e = low e'
                      \<and> i e < i e'
                      \<and> loop_update_action_post e e'"

definition dnfp_inv1:: "env \<Rightarrow> bool" where 
"dnfp_inv1  e \<equiv> dnfp_precondition e
                \<and> low_invariant_is_0_Env e"

definition dnfp_inv2:: "env \<Rightarrow> bool" where 
"dnfp_inv2 e \<equiv> dnfp_precondition e
                \<and> invariant_low_to_j_is_1_Env e"

definition dnfp_inv3:: "env \<Rightarrow> bool" where
"dnfp_inv3 e \<equiv> dnfp_precondition e
                \<and> high_invariant_is_2_Env e"

end