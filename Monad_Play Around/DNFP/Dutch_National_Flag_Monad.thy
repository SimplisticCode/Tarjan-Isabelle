theory Dutch_National_Flag_Monad
imports 
  Main
  "../State_Monad_HL"
  "HOL-Library.Multiset"
begin

text\<open>Monad definiti.ons to encode and extract data from the monad\<close>
datatype color = red | white | blue

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

section\<open>DNFP\<close>

definition swap:: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array" where
"swap l x y \<equiv> (if x < length l \<and> y < length l then l[x := l!y, y := l!x] else l)"

lemma length_swap: "length(swap l x y) = length l"
  by(simp add: swap_def)

lemma distinct_swap[simp]:
  "distinct(swap l x y) = distinct l"
  by(simp add: swap_def)

lemma mset_swap: "mset (swap l x y) = mset l"
  by (simp add: Dutch_National_Flag_Monad.swap_def mset_swap)

value\<open>swap [a,b,c,d,e] 0 4 = [e,b,c,d,a]\<close>

text\<open>Get i and get low seems not to be necessary\<close>
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
    } else (if s!j = 2 then do 
    {
      dec_highbound
    }
   else do {
      inc_index
   }))
  }"



text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
fun dnfp_mon:: "nat \<Rightarrow> (env, unit) state" where
"dnfp_mon 0  = skip"|
"dnfp_mon (Suc 0)  = skip"|
"dnfp_mon (Suc n)  = do {
                        (h, j) \<leftarrow> get (\<lambda>e. (high e, i e));
                        (if h > j then do{
                          loop_update_action;
                          dnfp_mon n
                         }
                       else skip
                      )}"


definition init_env:: "nat array \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

definition init_state_env:: "nat array \<Rightarrow> (env, unit) state" where
  "init_state_env l \<equiv> State (\<lambda>x. ((),init_env l))"

definition mk_rec:: "nat array \<Rightarrow>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> env" where
"mk_rec arr l j h \<equiv> \<lparr>high = h,            low = l,
                     i = j,               xs = arr\<rparr>"

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0]))))\<close>

section\<open>Definiton of all the Pre and postconditions\<close>

subsection\<open>The invariants are taken from https://en.wikipedia.org/wiki/Dutch_national_flag_problem\<close>
definition low_invariant_is_0 where
"low_invariant_is_0 arr l \<equiv> (\<forall>x. x < l \<longrightarrow> arr!x = 0)"

definition invariant_low_to_j_is_1 where
"invariant_low_to_j_is_1 arr l j \<equiv> (\<forall>x. (x \<ge> l \<and> x < j) \<longrightarrow> arr!x = 1)"

definition high_invariant_is_2 where
"high_invariant_is_2 arr h\<equiv> (\<forall>x. x \<ge> h \<longrightarrow> arr!x = 2)"

definition low_invariant_is_0_Env where
"low_invariant_is_0_Env e \<equiv> (\<forall>x. x < (low e) \<longrightarrow> (xs e)!x = 0)"

definition invariant_low_to_j_is_1_Env where
"invariant_low_to_j_is_1_Env e \<equiv> (\<forall>x. (x \<ge> (low e) \<and> x < (i e)) \<longrightarrow> (xs e)!x = 1)"

definition high_invariant_is_2_Env where
"high_invariant_is_2_Env e\<equiv> (\<forall>x. x \<ge> (high e) \<longrightarrow> (xs e)!x = 2)"

definition invariants_Env:: "env \<Rightarrow> bool" where
"invariants_Env e \<equiv> high_invariant_is_2_Env e
              \<and> invariant_low_to_j_is_1_Env e
              \<and> low_invariant_is_0_Env e"

definition invariants where
"invariants arr l j h\<equiv> low_invariant_is_0 arr l
              \<and> invariant_low_to_j_is_1 arr l j
              \<and> high_invariant_is_2 arr h"

text\<open>This can be used in the other pre and post-conditions for the methods inside loop_update_actions\<close>

subsection\<open>Pre- and Postconditions\<close>

subsubsection\<open>Pre-conditions\<close>
definition dnfp_pre where
"dnfp_pre e \<equiv> high e \<ge> i e
              \<and> i e \<ge> low e 
              \<and> length (xs e) \<ge> high e
              \<and> set (xs e) \<subseteq> {1,2,3}"

definition loop_update_action_pre:: "env \<Rightarrow> bool" where
"loop_update_action_pre e \<equiv> high e > i e
                             \<and> length (xs e) > (Suc 0)
                             \<and> length (xs e) \<ge> high e
                             \<and> low e < high e
                             \<and> low e \<le> i e"

definition loop_update_action_pre_aux:: "env \<Rightarrow> env \<Rightarrow> bool" where
"loop_update_action_pre_aux e s \<equiv> s = e
                              \<and> loop_update_action_pre e"

definition loop_update_action_inv1 where 
"loop_update_action_inv1 e \<equiv> loop_update_action_pre e 
                            \<and> low_invariant_is_0_Env e"

definition loop_update_action_inv2 where 
"loop_update_action_inv2 e \<equiv> loop_update_action_pre e 
                              \<and> invariant_low_to_j_is_1_Env e"

definition loop_update_action_inv3 where 
"loop_update_action_inv3 e \<equiv> loop_update_action_pre e 
                              \<and> high_invariant_is_2_Env e"

definition loop_update_action_post where
"loop_update_action_post e e' \<equiv> length (xs e) = length (xs e')
                                \<and> high e \<ge> high e'
                                \<and> low e \<le> low e'
                                \<and> i e \<le> i e'
                                \<and> high e - i e > high e' - i e'"

definition inc_lowbound_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_pre e s \<equiv> s = e
                        \<and> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1"

definition inc_lowbound_inv1 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv1 s \<equiv> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1
                        \<and> low_invariant_is_0_Env s"

definition inc_lowbound_inv2 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv2 s \<equiv> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1
                        \<and> invariant_low_to_j_is_1_Env s"

definition inc_lowbound_inv3 :: "env \<Rightarrow> bool" where
"inc_lowbound_inv3 s \<equiv> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1
                        \<and> high_invariant_is_2_Env s"

definition dec_highbound_pre where 
"dec_highbound_pre e s\<equiv> e = s
                        \<and> loop_update_action_pre e 
                        \<and> (xs e)!(i e) = 2"

definition dec_highbound_inv1 where 
"dec_highbound_inv1 e \<equiv> loop_update_action_pre e 
                        \<and> (xs e)!(i e) = 2
                        \<and> (xs e)!(high e) = 2
                        \<and> low_invariant_is_0_Env e"

definition dec_highbound_inv2 where 
"dec_highbound_inv2 e \<equiv> loop_update_action_pre e 
                        \<and> (xs e)!(i e) = 2
                        \<and> (xs e)!(high e) = 2
                        \<and> invariant_low_to_j_is_1_Env e"

definition dec_highbound_inv3 where 
"dec_highbound_inv3 e \<equiv> loop_update_action_pre e 
                        \<and> (xs e)!(i e) = 2
                        \<and> (xs e)!(high e) = 2
                        \<and> high_invariant_is_2_Env e"

definition inc_index_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_pre e s \<equiv> e = s 
                      \<and> loop_update_action_pre e
                      \<and> (xs e)!(i e) = 1"

definition inc_index_inv1:: "env \<Rightarrow> bool" where 
"inc_index_inv1 e \<equiv> loop_update_action_pre e
                    \<and> (xs e)!(i e) = 1
                    \<and> low_invariant_is_0_Env e"

definition inc_index_inv2:: "env \<Rightarrow> bool" where 
"inc_index_inv2 e \<equiv> loop_update_action_pre e
                    \<and> (xs e)!(i e) = 1
                        \<and> invariant_low_to_j_is_1_Env e"

definition inc_index_inv3:: "env \<Rightarrow> bool" where
"inc_index_inv3 e \<equiv> loop_update_action_pre e
                    \<and> (xs e)!(i e) = 1
                    \<and> high_invariant_is_2_Env e"

subsubsection\<open>Post-conditions\<close>
definition inc_lowbound_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_post e e'\<equiv> high e = high e'
                          \<and> low e < low e'
                          \<and> loop_update_action_post e e'
                          \<and> i e < i e'"

definition dec_highbound_post where 
"dec_highbound_post e e' \<equiv> length (xs e) > high e' 
                              \<and> high e = Suc (high e') 
                              \<and> low e = low e'
                              \<and> i e = i e'
                              \<and> (xs e')!(high e') = 2
                              \<and> loop_update_action_post e e'"

definition inc_index_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_post e e' \<equiv> high e = high e' 
                      \<and> low e = low e'
                      \<and> Suc(i e) = i e'
                      \<and> loop_update_action_post e e'"

text\<open>Is it after one iteration of after completion?\<close>
definition dnfp_post where 
"dnfp_post e e2 \<equiv> length (xs e) = length (xs e2)
                          \<and> high e \<ge> high e2
                          \<and> low e \<le> low e2
                          \<and> i e \<le> i e2
                          \<and> high e - i e > high e2 - i e2"

section\<open>Lemmas\<close>
subsection\<open>Hoare proofs\<close>

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
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x \<ge> high e. xs e ! x = 2)"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x \<ge> high e. xs e ! x = 2)"])
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
        (*I have had some problems to establish the seq_rule here*)
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


(*I don't know if you can prove this using the approach, since the invariant gets violated if it is broken up into steps*)
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


lemma update_aux1: "spec (\<lambda>xa. xa = e \<and> loop_update_action_pre e \<and> xs x = xs xa \<and> i x = i xa \<and> xs x ! i x = 0) inc_lowbound (\<lambda>x. loop_update_action_post e)"
  unfolding loop_update_action_pre_def loop_update_action_post_def 
  apply(simp add: inc_lowbound_def)
    apply(intro conj_rule_right)
      apply (intro get_rule; intro allI; simp)
 apply (intro seq_rule[of _ _ "(\<lambda>_ y. length (xs e) = length (xs y))"])
         apply (simp add: spec_def put_def get_state_def put_state_def xs_Env_def swap_def)
        apply (rule allI; intro get_rule; rule allI)
        apply (intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
         apply (simp add: spec_def put_def get_state_def put_state_def i_Env_def)
      apply (intro allI; simp)
        apply (intro get_rule; intro allI)
         apply (simp add: spec_def put_def get_state_def put_state_def low_Env_def)
                apply (intro get_rule; intro allI; simp)
                apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le>  high e)"]) 
                 apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def)
      apply (intro allI; simp)
       apply (intro get_rule; intro allI)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"]) 
        apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
      apply (intro allI; simp)
       apply (intro get_rule; intro allI)
        apply (simp add: spec_def get_def put_def get_state_def put_state_def low_Env_def)
       apply (intro get_rule; intro allI; simp)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"]) 
         apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def)
      apply (intro allI; simp)
       apply (intro get_rule; intro allI)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"]) 
         apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
      apply (intro allI; simp)
       apply (intro get_rule; intro allI)
         apply (simp add: spec_def get_def put_def get_state_def put_state_def low_Env_def)
     apply (intro get_rule; intro allI; simp)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"]) 
      apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def)
      apply (intro allI; simp)
          apply (intro get_rule; intro allI)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. i e < i y)"]) 
         apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
      apply (intro allI; simp)
       apply (intro get_rule; intro allI)
         apply (simp add: spec_def get_def put_def get_state_def put_state_def low_Env_def)
       apply (intro get_rule; intro allI; simp)
          apply(intro seq_rule[of _ _ "(\<lambda>x y. low y \<le> low e \<and> i e \<le> i y \<and> high y = high e)"]) 
         apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
      apply (intro allI; simp)
         apply (intro get_rule; intro allI; simp)
      apply(intro seq_rule[of _ _ "(\<lambda>x y. high e = high y \<and> i y > i e \<and> low y \<le> low e)"]) 
     apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
    apply (intro allI; simp)
     apply (intro get_rule; intro allI; simp)
  apply (simp add: spec_def get_def put_def get_state_def put_state_def low_Env_def return_def)
  sorry


subsection\<open>Loop update action\<close>
lemma loop_update_action_spec: "spec (loop_update_action_pre_aux e) loop_update_action (GG (loop_update_action_post e))"
  unfolding loop_update_action_pre_aux_def GG_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
  apply (intro cond_rule; simp)
  using update_aux1 apply blast
  unfolding loop_update_action_pre_def loop_update_action_post_def
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
    apply(simp add: inc_index_def)
    apply(intro conj_rule_right)
    apply (intro get_rule; intro allI; simp)
    apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
    apply (intro get_rule; intro allI; simp)
    apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
    apply (intro get_rule; intro allI; simp)
     apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
    apply (intro get_rule; intro allI; simp)
    apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
    apply (intro get_rule; intro allI; simp)
   apply (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)
  by(linarith)

subsubsection\<open>Invariants\<close>
text\<open>Should I add some more assumptions (The preconditions from the 3 methods inside loop_update_action) here in the precondition?\<close>
lemma loop_update_action_invariantRed: "spec loop_update_action_inv1 loop_update_action (GG low_invariant_is_0_Env)"
   unfolding loop_update_action_inv1_def loop_update_action_pre_def  GG_def low_invariant_is_0_Env_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule)
     apply(simp add: inc_lowbound_def)
     apply (intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. xs e ! low e = 0 \<and>  (\<forall>x<low e. xs e ! x = 0))"])
      apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
   apply auto[1]
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. xs e ! low e = 0 \<and> (\<forall>x<low e. xs e ! x = 0))"])
   apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
     apply (simp add: spec_def put_def put_state_def get_state_def low_Env_def)
   using less_antisym apply blast
     apply(simp add: dec_highbound_def)
     apply (intro get_rule; intro allI; simp)
      apply(intro seq_rule[of _ _ "(\<lambda>x e. (\<forall>x<low e. xs e ! x = 0) \<and> high e \<le> length (xs e) \<and> high e \<ge> i e \<and> low e \<le> i e)"]) 
       apply (simp add: spec_def get_def put_def get_state_def put_state_def high_Env_def)
       apply(linarith)
      apply(intro allI; simp)
     apply (intro get_rule; intro allI; simp)
      apply (simp add: spec_def get_def put_def get_state_def put_state_def xs_Env_def swap_def)
     apply(simp add: inc_index_def)
     apply (intro get_rule; intro allI; simp)
   by (simp add: spec_def get_def put_def get_state_def put_state_def i_Env_def)

lemma loop_update_action_invariantWhite: "spec loop_update_action_inv2 loop_update_action (GG invariant_low_to_j_is_1_Env)"
   unfolding loop_update_action_inv2_def loop_update_action_pre_def  GG_def invariant_low_to_j_is_1_Env_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule)
     apply(simp add: inc_lowbound_def)
     apply (intro get_rule; intro allI; simp)
   apply (simp add: spec_def put_def put_state_def  get_state_def xs_Env_def swap_def get_def i_Env_def low_Env_def return_def)
   apply(intro allI)
     apply (simp add: nth_list_update)
     apply(simp add: dec_highbound_def)
        apply(intro get_rule; intro allI; simp)
    apply(intro seq_rule[of _ _ "(\<lambda>x e. low e \<le> i e \<and> high e \<ge> i e \<and> length (xs e) > high e \<and> (\<forall>x. low e \<le> x \<and> x < i e \<longrightarrow> xs e ! x = Suc 0))"])
     apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def swap_def)
    apply linarith
     apply(intro allI; simp)
    apply(intro get_rule;intro allI; simp)
   apply (simp add: spec_def put_def put_state_def get_state_def xs_Env_def swap_def)
     apply(simp add: inc_index_def)
    apply(intro get_rule;intro allI; simp)
   apply (simp_all add: spec_def put_def put_state_def get_state_def i_Env_def)
   using less_SucE by blast

lemma loop_update_action_invariantBlue: "spec loop_update_action_inv3 loop_update_action (GG high_invariant_is_2_Env)"
   unfolding loop_update_action_inv3_def loop_update_action_pre_def  GG_def high_invariant_is_2_Env_def
  apply(simp add: loop_update_action_def)
  apply (intro get_rule; intro allI; clarify)
   apply (intro cond_rule)
     apply(simp add: inc_lowbound_def) 
     apply(intro get_rule;intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x \<ge> high e. xs e ! x = 2)"])
   apply (simp add: spec_def put_def put_state_def swap_def get_state_def xs_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. \<forall>x \<ge> high e. xs e ! x = 2)"])
   apply (simp add: spec_def put_def put_state_def get_state_def i_Env_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
     apply (simp add: spec_def put_def put_state_def get_state_def low_Env_def)
   apply(simp add: dec_highbound_def) 
    apply(intro get_rule; intro allI; simp)
     apply (simp add: spec_def put_def put_state_def get_state_def high_Env_def xs_Env_def swap_def get_def return_def)
    apply(intro allI)
   apply (smt Suc_leI Suc_pred diff_is_0_eq' leD le_eq_less_or_eq length_list_update less_imp_diff_less nth_list_update nth_list_update_neq)
   apply(simp add: inc_index_def) 
    apply(intro get_rule; intro allI; simp)
   by (simp add: spec_def put_def put_state_def get_state_def i_Env_def)

subsection\<open>DNFP proof\<close>
(*How to apply this method*)
lemma dnfp_prepost: "spec (dnfp_pre e) (dnfp_mon n) (GG (dnfp_post e))"
  apply(induction n rule:dnfp_mon.induct)
  apply(simp add: mk_rec_def dnfp_pre_def snd_def dnfp_post_def high_invariant_is_2_def loop_update_action_post_def)
   apply force
  apply(simp add: mk_rec_def dnfp_pre_def snd_def dnfp_post_def high_invariant_is_2_def loop_update_action_post_def)
   apply force
  apply(simp)

end