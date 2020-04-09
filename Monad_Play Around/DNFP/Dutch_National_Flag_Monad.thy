theory Dutch_National_Flag_Monad
imports 
  Main
  "../State_Monad_HL"
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

value\<open>swap [a,b,c,d,e] 0 4 = [e,b,c,d,a]\<close>

definition init_loop where
"init_loop \<equiv> do{
                  h \<leftarrow> get high;
                  j \<leftarrow> get i;
                  return (h, j)
                }"

definition inc_lowbound where
"inc_lowbound \<equiv> do{
                  l \<leftarrow> get low;  
                  s \<leftarrow> get xs;  
                  j \<leftarrow> get i;                                   
                  put xs_Env (swap s j l);
                  put i_Env (Suc j);
                  put low_Env (Suc l)
                }"

definition add_high where
"add_high \<equiv> do{
                s \<leftarrow> get xs;
                j \<leftarrow> get i;
                h \<leftarrow> get high;
                put xs_Env (swap s j h)
              }"

definition dec_highbound where
"dec_highbound \<equiv> do{
                    h \<leftarrow> get high;
                    put high_Env (h - 1);
                    add_high
                }"

definition inc_index where
"inc_index \<equiv> do{
                  j \<leftarrow> get i;
                  put i_Env (Suc j)
                }"

definition loop_update_action where
"loop_update_action \<equiv> 
do{
  s \<leftarrow> get xs;
  j \<leftarrow> get i;
  (if s!j < 1 then do {
    inc_lowbound
  }else (if s!j > 1 then do 
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
                        h \<leftarrow> get high;
                        j \<leftarrow> get i;
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
              \<and> length (xs e) \<ge> high e"

definition loop_update_action_pre where
"loop_update_action_pre e \<equiv>  high e > i e
                              \<and> length (xs e) > (Suc 0)
                              \<and> length (xs e) \<ge> high e
                              \<and> low e < high e
                              \<and> low e \<le> i e"

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
"dec_highbound_pre \<equiv> \<lambda>e. loop_update_action_pre e 
                              \<and> (xs e)!(i e) = 2
                              \<and> (xs e)!(high e) = 2"

definition inc_index_pre where 
"inc_index_pre  \<equiv> \<lambda>e. loop_update_action_pre e
                      \<and> (xs e)!(i e) = 1"

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

definition inc_index_post where 
"inc_index_post e e' \<equiv> high e = high e' 
                      \<and> low e = low e'
                      \<and> Suc(i e) = i e'
                      \<and> loop_update_action_post e e'"

definition dnfp_post where 
"dnfp_post e e2 \<equiv> length (xs e) = length (xs e2)
                  \<and> length (xs e) > (Suc 0) \<longrightarrow> (inc_index_post e e2  \<or> dec_highbound_post e e2 \<or> inc_lowbound_post e e2)"

section\<open>Lemmators\<close>
subsection\<open>Hoare proofs\<close>

lemma inc_lowbound_spec: "spec (inc_lowbound_pre e) inc_lowbound (GG (inc_lowbound_post e))"
  apply(simp_all add: inc_lowbound_def)
  apply(simp add: inc_lowbound_pre_def loop_update_action_pre_def get_def get_state_def)
  apply (simp_all add: spec_def  get_def get_state_def return_def put_def put_state_def GG_def)
  apply(simp_all add: inc_lowbound_pre_def loop_update_action_pre_def inc_lowbound_post_def loop_update_action_post_def swap_def xs_Env_def i_Env_def low_Env_def)
  by linarith

subsubsection\<open>Invariants\<close>
lemma inc_lowbound_invariantRed: "spec inc_lowbound_inv1 inc_lowbound (GG low_invariant_is_0_Env)"
  apply(simp_all add: inc_lowbound_def)
  apply (simp_all add: inc_lowbound_inv1_def loop_update_action_pre_def low_invariant_is_0_Env_def spec_def  get_def get_state_def return_def put_def put_state_def GG_def)
  apply(simp add: low_Env_def i_Env_def xs_Env_def swap_def)
  using less_Suc_eq by auto

lemma inc_lowbound_invariantWhite: "spec inc_lowbound_inv2  inc_lowbound (GG invariant_low_to_j_is_1_Env)"
  apply(simp_all add: inc_lowbound_def)
  apply (simp_all add: inc_lowbound_inv2_def loop_update_action_pre_def invariant_low_to_j_is_1_Env_def spec_def  get_def get_state_def return_def put_def put_state_def GG_def)
  apply(simp add: low_Env_def i_Env_def xs_Env_def swap_def)
  using less_Suc_eq by auto

lemma inc_lowbound_invariantBlue: "spec inc_lowbound_inv3  inc_lowbound (GG high_invariant_is_2_Env)"
  apply(simp_all add: inc_lowbound_def)
  apply (simp_all add: inc_lowbound_inv3_def loop_update_action_pre_def high_invariant_is_2_Env_def spec_def  get_def get_state_def return_def put_def put_state_def GG_def)
  by(simp add: low_Env_def i_Env_def xs_Env_def swap_def)

definition inc_lowbound_inv :: "env \<Rightarrow> bool" where
"inc_lowbound_inv s \<equiv> (inc_lowbound_inv3 s \<and> inc_lowbound_inv2 s \<and> inc_lowbound_inv1 s)"

lemma inc_lowbound_invariants: "spec inc_lowbound_inv  inc_lowbound (GG invariants_Env)"
  by (metis (mono_tags, lifting) GG_def inc_lowbound_inv_def inc_lowbound_invariantBlue inc_lowbound_invariantRed inc_lowbound_invariantWhite invariants_Env_def spec_def split_def)

subsection\<open>Dec_highbound Invariants\<close>
lemma dec_highbound_prepost[simp]: "\<lbrakk>dec_highbound_pre arr l j h; (mk_rec arr l j h) = e; snd(run_state (dec_highbound arr j h) e) = e2 \<rbrakk> \<Longrightarrow> dec_highbound_post e e2"
  apply(simp_all add: dec_highbound_pre_def init_loop_pre_def mk_rec_def loop_update_action_pre_def dec_highbound_post_def snd_def loop_update_action_post_def dec_highbound_def)
  apply(simp_all add: put_high_def add_high_def set_high_def put_xs_def put_def get_def swap_def set_xs_def)
  by(auto)

subsubsection\<open>Invariants\<close>
lemma dec_highbound_invariantRed: "\<lbrakk>dec_highbound_pre arr l j h; (mk_rec arr l j h) = e; low_invariant_is_0 (xs e) (low e);snd(run_state (dec_highbound arr j h) e) = e2 \<rbrakk> \<Longrightarrow> low_invariant_is_0 (xs e2) (low e2)"
apply(simp_all add: dec_highbound_pre_def mk_rec_def loop_update_action_pre_def low_invariant_is_0_def snd_def loop_update_action_post_def dec_highbound_def)
  apply(simp_all add: put_high_def add_high_def set_high_def put_xs_def put_def get_def swap_def set_xs_def)
  by (auto)

lemma dec_highbound_invariantWhite: "\<lbrakk>dec_highbound_pre arr l j h; (mk_rec arr l j h) = e; invariant_low_to_j_is_1 (xs e) (low e) (i e);snd(run_state (dec_highbound arr j h) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2)"
apply(simp_all add: dec_highbound_pre_def init_loop_pre_def mk_rec_def loop_update_action_pre_def invariant_low_to_j_is_1_def snd_def loop_update_action_post_def dec_highbound_def)
  apply(simp_all add: put_high_def add_high_def set_high_def put_xs_def put_def get_def swap_def set_xs_def)
  by (auto)

lemma dec_highbound_invariantBlue: "\<lbrakk>dec_highbound_pre arr l j h; (mk_rec arr l j h) = e; high_invariant_is_2 (xs e) (high e);snd(run_state (dec_highbound arr j h) e) = e2 \<rbrakk> \<Longrightarrow> high_invariant_is_2 (xs e2) (high e2)"
apply(simp_all add: dec_highbound_pre_def init_loop_pre_def mk_rec_def loop_update_action_pre_def high_invariant_is_2_def snd_def loop_update_action_post_def dec_highbound_def)
  apply(simp_all add: put_high_def add_high_def set_high_def put_xs_def put_def get_def swap_def set_xs_def)
  by (smt Suc_pred le_less_Suc_eq length_list_update not_less not_less_eq nth_list_update nth_list_update_neq select_convs(1) select_convs(4) zero_less_Suc)

lemma dec_highbound_inv: "\<lbrakk>dec_highbound_pre arr l j h; (mk_rec arr l j h) = e; invariant_low_to_j_is_1 (xs e) (low e) (i e); high_invariant_is_2 (xs e) (high e);
                        low_invariant_is_0 (xs e) (low e); snd(run_state (dec_highbound arr j h) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2) \<and> low_invariant_is_0 (xs e2) (low e2) \<and> high_invariant_is_2 (xs e2) (high e2)"
  using dec_highbound_invariantBlue dec_highbound_invariantRed dec_highbound_invariantWhite by blast

subsection\<open>Inc_index Invariants\<close>
lemma inc_index_prepost: "\<lbrakk>inc_index_pre arr l j h;  (mk_rec arr l j h) = e; snd(run_state (inc_index j) e) = e2\<rbrakk> \<Longrightarrow> inc_index_post e e2"
  apply(simp_all add: snd_def mk_rec_def init_loop_pre_def inc_index_def inc_index_post_def inc_index_pre_def loop_update_action_pre_def loop_update_action_post_def)
  apply(simp_all add: invariants_def low_invariant_is_0_def invariant_low_to_j_is_1_def high_invariant_is_2_def put_i_def get_def set_i_def put_def)
  by (auto)

subsubsection\<open>Invariants\<close>
lemma inc_index_invariantRed: "\<lbrakk>inc_index_pre arr l j h; (mk_rec arr l j h) = e; low_invariant_is_0 (xs e) (low e);snd(run_state (inc_index j) e) = e2 \<rbrakk> \<Longrightarrow> low_invariant_is_0 (xs e2) (low e2)"
apply(simp_all add: inc_index_def mk_rec_def loop_update_action_pre_def low_invariant_is_0_def snd_def loop_update_action_post_def inc_lowbound_def)
  apply(simp_all add: put_xs_def get_low_def put_i_def swap_def return_def get_def put_def put_low_def set_low_def set_i_def set_xs_def)
  by (auto)

lemma inc_index_invariantBlue: "\<lbrakk>inc_index_pre arr l j h; (mk_rec arr l j h) = e; high_invariant_is_2 (xs e) (high e);snd(run_state (inc_index j) e) = e2 \<rbrakk> \<Longrightarrow> high_invariant_is_2 (xs e2) (high e2)"
apply(simp_all add: inc_index_def mk_rec_def loop_update_action_pre_def high_invariant_is_2_def snd_def loop_update_action_post_def inc_lowbound_def)
  apply(simp_all add: put_xs_def get_low_def put_i_def swap_def return_def get_def put_def put_low_def set_low_def set_i_def set_xs_def)
  by (auto)

lemma inc_index_invariantWhite: "\<lbrakk>inc_index_pre arr l j h; (mk_rec arr l j h) = e; invariant_low_to_j_is_1 (xs e) (low e) (i e);snd(run_state (inc_index j) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2)"
apply(simp_all add: inc_index_def mk_rec_def loop_update_action_pre_def invariant_low_to_j_is_1_def snd_def loop_update_action_post_def inc_lowbound_def)
  apply(simp_all add: put_xs_def get_low_def put_i_def swap_def return_def get_def put_def put_low_def set_low_def set_i_def set_xs_def)
  by (metis One_nat_def inc_index_pre_def less_Suc_eq select_convs(2) select_convs(3) select_convs(4))

lemma inc_index_inv: "\<lbrakk>inc_index_pre arr l j h; (mk_rec arr l j h) = e; invariant_low_to_j_is_1 (xs e) (low e) (i e); high_invariant_is_2 (xs e) (high e);
                        low_invariant_is_0 (xs e) (low e); snd(run_state (inc_index j) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2) \<and> low_invariant_is_0 (xs e2) (low e2) \<and> high_invariant_is_2 (xs e2) (high e2)"
  using inc_index_invariantBlue inc_index_invariantRed inc_index_invariantWhite by blast

subsection\<open>Loop update action\<close>
lemma loop_update_action_prepost: "\<lbrakk>(mk_rec arr l j h) = e; loop_update_action_pre e; snd(run_state (loop_update_action arr j h) e) = e2 \<rbrakk> \<Longrightarrow> loop_update_action_post e e2"
  apply(simp_all add:  mk_rec_def loop_update_action_pre_def init_loop_pre_def snd_def loop_update_action_post_def loop_update_action_def)
  apply(simp_all only: inc_lowbound_def dec_highbound_def inc_index_def get_gen_def put_high_def set_high_def put_xs_def put_def get_def swap_def)
  apply(simp_all only: set_low_def put_low_def set_xs_def put_i_def add_high_def put_def get_def set_i_def put_xs_def swap_def)
  apply(simp only: return_def)
  by(auto)

subsubsection\<open>Invariants\<close>
lemma  loop_update_action_invariantRed: "\<lbrakk>(mk_rec arr l j h) = e; loop_update_action_pre e; inc_lowbound_pre arr l j h \<or> dec_highbound_pre arr l j h \<or> inc_index_pre arr l j h; low_invariant_is_0 (xs e) (low e);snd(run_state (loop_update_action arr j h) e) = e2 \<rbrakk> \<Longrightarrow> low_invariant_is_0 (xs e2) (low e2)"
  using dec_highbound_invariantRed inc_index_invariantRed inc_index_pre_def inc_lowbound_invariantRed inc_lowbound_pre_def loop_update_action_def by fastforce

lemma  loop_update_action_invariantBlue: "\<lbrakk>(mk_rec arr l j h) = e; loop_update_action_pre e; inc_lowbound_pre arr l j h \<or> dec_highbound_pre arr l j h \<or> inc_index_pre arr l j h;  high_invariant_is_2 (xs e) (high e);snd(run_state (loop_update_action arr j h) e) = e2 \<rbrakk> \<Longrightarrow> high_invariant_is_2 (xs e2) (high e2)"
  using dec_highbound_invariantBlue inc_index_invariantBlue inc_index_pre_def inc_lowbound_invariantBlue inc_lowbound_pre_def loop_update_action_def by fastforce

lemma  loop_update_action_invariantWhite: "\<lbrakk>(mk_rec arr l j h) = e; loop_update_action_pre e; inc_lowbound_pre arr l j h \<or> dec_highbound_pre arr l j h \<or> inc_index_pre arr l j h; invariant_low_to_j_is_1 (xs e) (low e) (i e);snd(run_state (loop_update_action arr j h) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2)"
  using dec_highbound_invariantWhite inc_index_invariantWhite inc_index_pre_def inc_lowbound_invariantWhite inc_lowbound_pre_def loop_update_action_def by fastforce

text\<open>The difference between high and i will never increase and will be decreased by loop_update_action\<close>
lemma termination_loop_update_action:
"\<lbrakk>(mk_rec arr l j h) = e; loop_update_action_pre e; snd(run_state (loop_update_action arr j h) e) = e2 \<rbrakk> \<Longrightarrow> (high e2 - i e2) < (high e - i e)"
  using loop_update_action_post_def loop_update_action_prepost by blast

subsection\<open>Init_loop\<close>
lemma init_loop_prepost: "\<lbrakk>init_loop_pre e; snd(run_state (init_loop) e) = e2\<rbrakk> \<Longrightarrow> init_loop_post e e2"
  by(simp_all add: init_loop_pre_def snd_def init_loop_def init_loop_post_def get_gen_def get_def return_def)

subsubsection\<open>Invariants\<close>
text\<open>This is a very since proof since the method does not change any state at all\<close>
lemma init_loop_inv: "\<lbrakk>init_loop_pre e; invariant_low_to_j_is_1 (xs e) (low e) (i e); high_invariant_is_2 (xs e) (high e);
                        low_invariant_is_0 (xs e) (low e); snd(run_state (init_loop) e) = e2 \<rbrakk> \<Longrightarrow> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2) \<and> low_invariant_is_0 (xs e2) (low e2) \<and> high_invariant_is_2 (xs e2) (high e2)"
  by (metis init_loop_post_def init_loop_prepost)

subsection\<open>DNFP proof\<close>
lemma dnfp_prepost: "\<lbrakk>(mk_rec arr l j h) = e; dnfp_pre e; dnfp_pre_aux e; length arr = n; snd(run_state (dnfp_mon n) e) = e2 \<rbrakk> \<Longrightarrow> dnfp_post e e2"
  apply(induction n rule:dnfp_mon.induct)
  apply(simp add: mk_rec_def dnfp_pre_def snd_def dnfp_post_def high_invariant_is_2_def loop_update_action_post_def)
   apply force
  apply(simp add: mk_rec_def dnfp_pre_def snd_def dnfp_post_def high_invariant_is_2_def loop_update_action_post_def)
   apply force
  apply(simp)

end