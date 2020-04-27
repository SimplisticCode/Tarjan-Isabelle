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

subsection\<open>Monad update functions\<close>
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

section\<open>Invariants definitions\<close>
text\<open>The invariants are taken from https://en.wikipedia.org/wiki/Dutch_national_flag_problem\<close>
definition low_invariant_is_0_Env where
"low_invariant_is_0_Env e \<equiv> (\<forall>x. x < (low e) \<longrightarrow> (xs e)!x = 0)"

definition invariant_low_to_j_is_1_Env where
"invariant_low_to_j_is_1_Env e \<equiv> (\<forall>x. (x \<ge> (low e) \<and> x < (i e)) \<longrightarrow> (xs e)!x = 1)"

definition high_invariant_is_2_Env where
"high_invariant_is_2_Env e\<equiv> (\<forall>x. x \<ge> (high e) \<and> x < length (xs e) \<longrightarrow> (xs e)!x = 2)"

section\<open>General DNFP conditions\<close>
text\<open>This relationship between the variables should always hold\<close>
definition dnfp_variables_invariants:: "env \<Rightarrow> bool" where
"dnfp_variables_invariants e \<equiv> high e \<ge> i e
                      \<and> i e \<ge> low e 
                      \<and> length (xs e) \<ge> high e
                      \<and> set (xs e) \<subseteq> {0,1,2}"

definition dnfp_post where 
"dnfp_post e e2 \<equiv> length (xs e) = length (xs e2)
                  \<and> high e \<ge> high e2
                  \<and> low e \<le> low e2
                  \<and> i e \<le> i e2
                  \<and> high e - i e \<ge> high e2 - i e2
                  \<and> mset (xs e) = mset (xs e2)"

subsection\<open>DNFP invariants\<close>
definition dnfp_inv1:: "env \<Rightarrow> bool" where 
"dnfp_inv1  e \<equiv> dnfp_variables_invariants e
                \<and> low_invariant_is_0_Env e"

definition dnfp_inv2:: "env \<Rightarrow> bool" where 
"dnfp_inv2 e \<equiv> dnfp_variables_invariants e
                \<and> invariant_low_to_j_is_1_Env e"

definition dnfp_inv3:: "env \<Rightarrow> bool" where
"dnfp_inv3 e \<equiv> dnfp_variables_invariants e
                \<and> high_invariant_is_2_Env e"

definition dnfp_mon_inv :: "env \<Rightarrow> bool" where
"dnfp_mon_inv e \<equiv> ((dnfp_inv3 e) \<and> (dnfp_inv2 e) \<and> (dnfp_inv1 e))"

definition dnfp_post_final_spec where
"dnfp_post_final_spec e \<equiv> dnfp_mon_inv e \<and> i e = high e"

definition dnfp_mon_spec where
"dnfp_mon_spec e \<equiv> dnfp_variables_invariants e
                    \<and> dnfp_mon_inv e"

subsection\<open>Loop update action definitions\<close>
text\<open>These definitions rely on the definitions on dnfp, but in the precondition they have an extra assumption that gets inferred from the conditions-statement inside the function\<close>
text\<open>The post-condition is also for each of the definitions a little stronger compared to the more general\<close>

definition loop_update_action_pre:: "env \<Rightarrow> bool" where
"loop_update_action_pre e \<equiv> dnfp_variables_invariants e \<and> high e > i e"

definition loop_update_action_pre_aux:: "env \<Rightarrow> env \<Rightarrow> bool" where
"loop_update_action_pre_aux e s \<equiv> s = e
                              \<and> loop_update_action_pre e"

definition loop_update_action_post where
"loop_update_action_post e e' \<equiv> dnfp_post e e'
                                \<and> high e - i e = Suc(high e' - i e')"

subsubsection\<open>Loop update action Invariants\<close>
definition loop_update_action_inv1 where 
"loop_update_action_inv1 e \<equiv> dnfp_variables_invariants e 
                            \<and> low_invariant_is_0_Env e"

definition loop_update_action_inv2 where 
"loop_update_action_inv2 e \<equiv> dnfp_variables_invariants e 
                              \<and> invariant_low_to_j_is_1_Env e"

definition loop_update_action_inv3 where 
"loop_update_action_inv3 e \<equiv> dnfp_variables_invariants e 
                              \<and> high_invariant_is_2_Env e"

definition loop_update_action_inv :: "env \<Rightarrow> bool" where
"loop_update_action_inv s \<equiv> (loop_update_action_inv3 s \<and> loop_update_action_inv2 s \<and> loop_update_action_inv1 s)"

text\<open>The aux methods extend the inv with the property that can be inferred from the conditional-statement before the loop_update_action call\<close>
definition loop_update_action_inv1_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv1_aux e \<equiv> loop_update_action_inv1 e \<and> loop_update_action_pre e"

definition loop_update_action_inv2_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv2_aux e \<equiv> loop_update_action_inv2 e \<and> loop_update_action_pre e"

definition loop_update_action_inv3_aux:: "env \<Rightarrow> bool" where
"loop_update_action_inv3_aux e \<equiv> loop_update_action_inv3 e \<and> loop_update_action_pre e"     

definition loop_update_action_inv_aux :: "env \<Rightarrow> bool" where
"loop_update_action_inv_aux s \<equiv> (loop_update_action_inv s \<and> loop_update_action_pre s)"

section\<open> Definitions of methods/definitions inside Loop_update action\<close>
text\<open>These definitions rely on the definitions on loop_update_action, but in the precondition they have an extra assumption that gets inferred from the conditions-statement inside loop_update_action\<close>
text\<open>The post-condition is also for each of the definitions a little stronger compared to the more general loop_update_action_post\<close>

subsection\<open>Inc Lowbound definitions\<close>

definition inc_lowbound_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_pre e s \<equiv> s = e
                        \<and> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1"

definition inc_lowbound_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_post e e'\<equiv> high e = high e'
                          \<and> low e < low e'
                          \<and> loop_update_action_post e e'
                          \<and> i e < i e'"

subsubsection\<open>Inc Index invariants\<close>

definition inc_lowbound_inv1 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv1 s \<equiv> dnfp_variables_invariants s
                        \<and> low_invariant_is_0_Env s"

definition inc_lowbound_inv2 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv2 s \<equiv> dnfp_variables_invariants s
                        \<and> invariant_low_to_j_is_1_Env s"

definition inc_lowbound_inv3 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv3 s \<equiv> dnfp_variables_invariants s
                        \<and> high_invariant_is_2_Env s"

definition inc_lowbound_inv :: "env \<Rightarrow> bool" where
"inc_lowbound_inv s \<equiv> (inc_lowbound_inv3 s \<and> inc_lowbound_inv2 s \<and> inc_lowbound_inv1 s)"

text\<open>The aux methods extend the inv with the property that can be inferred from the conditional-statement before the function call\<close>
definition inc_lowbound_inv1_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv1_aux e \<equiv> inc_lowbound_inv1 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

definition inc_lowbound_inv2_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv2_aux e \<equiv> inc_lowbound_inv2 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

definition inc_lowbound_inv3_aux:: "env \<Rightarrow> bool" where
"inc_lowbound_inv3_aux e \<equiv> inc_lowbound_inv3 e \<and> loop_update_action_pre e \<and> xs e ! i e < 1"

definition inc_lowbound_inv_pre :: "env \<Rightarrow> bool" where
"inc_lowbound_inv_pre s \<equiv> (inc_lowbound_inv s \<and> loop_update_action_pre s \<and> xs s ! i s < 1)"


subsection\<open>Dec Highbound definitions\<close>
definition dec_highbound_pre where 
"dec_highbound_pre e s\<equiv> e = s
                        \<and> loop_update_action_pre e 
                        \<and> (xs e)!(i e) > 1"

definition dec_highbound_post where 
"dec_highbound_post e e' \<equiv> length (xs e') > high e' 
                              \<and> high e > high e' 
                              \<and> low e = low e'
                              \<and> i e = i e'
                              \<and> (xs e')!(high e') = 2
                              \<and> loop_update_action_post e e'"

subsubsection\<open>Dec Highbound invariants\<close>
definition dec_highbound_inv1 where 
"dec_highbound_inv1 e \<equiv> dnfp_variables_invariants e 
                        \<and> low_invariant_is_0_Env e"

definition dec_highbound_inv2 where 
"dec_highbound_inv2 e \<equiv> dnfp_variables_invariants e 
                        \<and> invariant_low_to_j_is_1_Env e"

definition dec_highbound_inv3 where 
"dec_highbound_inv3 e \<equiv> dnfp_variables_invariants e 
                        \<and> high_invariant_is_2_Env e"

definition dec_highbound_inv :: "env \<Rightarrow> bool" where
"dec_highbound_inv s \<equiv> (dec_highbound_inv3 s \<and> dec_highbound_inv2 s \<and> dec_highbound_inv1 s)"

text\<open>The aux methods extend the inv with the property that can be inferred from the conditional-statement before the function call\<close>

definition dec_highbound_inv1_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv1_aux e \<equiv> dec_highbound_inv1 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

definition dec_highbound_inv2_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv2_aux e \<equiv> dec_highbound_inv2 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

definition dec_highbound_inv3_aux:: "env \<Rightarrow> bool" where
"dec_highbound_inv3_aux e \<equiv> dec_highbound_inv3 e \<and> loop_update_action_pre e \<and> xs e ! i e > 1"

definition dec_highbound_inv_aux :: "env \<Rightarrow> bool" where
"dec_highbound_inv_aux s \<equiv> (dec_highbound_inv s \<and>  loop_update_action_pre s \<and> xs s ! i s > 1 )"


subsection\<open>Inc index definitions\<close>
definition inc_index_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_pre e s \<equiv> e = s 
                      \<and> loop_update_action_pre e
                      \<and> \<not>(xs e)!(i e) > 1
                      \<and> \<not>(xs e)!(i e) < 1"

definition inc_index_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_post e e' \<equiv> high e = high e' 
                      \<and> low e = low e'
                      \<and> i e < i e'
                      \<and> loop_update_action_post e e'"

subsubsection\<open>Inc index invariants\<close>
definition inc_index_inv1:: "env \<Rightarrow> bool" where 
"inc_index_inv1 e \<equiv> dnfp_variables_invariants e
                      \<and> low_invariant_is_0_Env e"


definition inc_index_inv2:: "env \<Rightarrow> bool" where 
"inc_index_inv2 e \<equiv> dnfp_variables_invariants e
                      \<and> invariant_low_to_j_is_1_Env e"

definition inc_index_inv3:: "env \<Rightarrow> bool" where
"inc_index_inv3 e \<equiv> dnfp_variables_invariants e
                    \<and> high_invariant_is_2_Env e"

definition inc_index_inv :: "env \<Rightarrow> bool" where
"inc_index_inv s \<equiv> (inc_index_inv3 s \<and> inc_index_inv2 s \<and> inc_index_inv1 s)"

text\<open>The aux methods extend the inv with the property that can be inferred from the conditional-statement before the function call\<close>
definition inc_index_inv1_aux:: "env \<Rightarrow> bool" where
"inc_index_inv1_aux e \<equiv> inc_index_inv1 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

definition inc_index_inv2_aux:: "env \<Rightarrow> bool" where
"inc_index_inv2_aux e \<equiv> inc_index_inv2 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"         

definition inc_index_inv3_aux:: "env \<Rightarrow> bool" where
"inc_index_inv3_aux e \<equiv> inc_index_inv3 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

definition inc_index_inv_aux:: "env \<Rightarrow> bool" where
"inc_index_inv_aux e \<equiv> inc_index_inv e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1 \<and> loop_update_action_pre e"

end