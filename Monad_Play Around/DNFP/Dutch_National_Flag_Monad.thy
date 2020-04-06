theory Dutch_National_Flag_Monad
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin

text\<open>Monad definitions to encode and extract data from the monad\<close>
datatype color = red | white | blue
section\<open>Monad definitions\<close>
record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat list"
  
definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(env, env) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "env \<Rightarrow> (env, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition get_gen:: "(env \<Rightarrow> 'b) \<Rightarrow> (env, 'b) state" where "get_gen acc = do { x \<leftarrow> get; return (acc  x)}"
definition get_high:: "(env, nat) state" where "get_high = do { x \<leftarrow> get; return (high  x) }" 
definition get_low:: "(env, nat) state" where "get_low = do { x \<leftarrow> get; return (low x) }" 
definition get_i:: "(env, nat) state" where "get_i = do { x \<leftarrow> get; return (i x) }" 
definition get_xs:: "(env, nat list) state" where "get_xs = do { x \<leftarrow> get; return (xs x) }" 
definition set_high:: "env \<Rightarrow> nat \<Rightarrow> env" where "set_high v x =  
\<lparr>            high = x,
             low = low v,
             i = i v,
             xs = xs v \<rparr>"
definition set_low:: "env \<Rightarrow> nat \<Rightarrow> env" where "set_low v x =  
\<lparr>            high = high v,
             low = x,
             i = i v,
             xs = xs v \<rparr>"
definition set_i:: "env \<Rightarrow> nat \<Rightarrow> env" where "set_i v x =  
\<lparr>            high = high v,
             low = low v,
             i = x,
             xs = xs v \<rparr>"
definition set_xs:: "env \<Rightarrow> nat list \<Rightarrow> env" where "set_xs v x =
\<lparr>            high = high v,
             low = low v,
             i = i v,
             xs = x \<rparr>"

definition put_high:: "nat \<Rightarrow> (env, unit) state" where "put_high x = do { v \<leftarrow> get; put (set_high v x) }"
definition put_low:: "nat \<Rightarrow> (env, unit) state" where "put_low x = do { v \<leftarrow> get; put (set_low v x) }"
definition put_i:: "nat \<Rightarrow> (env, unit) state" where "put_i x = do { v \<leftarrow> get; put (set_i v x) }"
definition put_xs:: "nat list \<Rightarrow> (env, unit) state" where "put_xs x = do { v \<leftarrow> get; put (set_xs v x) }"
definition skip:: "(env, unit) state" where "skip = State (\<lambda>x. ((),x))"

section\<open>DNFP\<close>

type_synonym 'a array = "'a list"

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
                  h \<leftarrow> get_high;
                  i \<leftarrow> get_i;
                  s \<leftarrow> get_xs;
                  return (h, i, s)
                }"

definition inc_lowbound where
"inc_lowbound s x\<equiv> do{
                  l \<leftarrow> get_low;                                       
                  put_xs (swap s x l);
                  put_i (Suc x);
                  put_low (Suc l)
                }"

definition add_high where
"add_high s j h \<equiv> do{
                    put_xs (swap s j h)
                  }"

definition dec_highbound where
"dec_highbound s j h \<equiv> do{
                    put_high (h - 1);
                    add_high s j (h-1)
                }"

definition inc_index where
"inc_index j \<equiv> do{
                  put_i (Suc j)
                }"
(*
definition hoare_def where
"hoare_def pre prog post \<equiv> "
*)

definition loop_update_action where
"loop_update_action s j h \<equiv> 
do{
  (if s!j < 1 then do {
    inc_lowbound s j
  }else (if s!j > 1 then do
  {
    dec_highbound s j h
  }
 else do {
    inc_index j
 }))
}"

text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
(*\<comment> l < high \<and> i < h*)
fun dnfp_mon:: "nat \<Rightarrow> (env, unit) state" where
"dnfp_mon 0  = skip"|
"dnfp_mon (Suc 0)  = skip"|
"dnfp_mon (Suc n)  = do {
                      (h, i, s) \<leftarrow> init_loop;
                        (if h > i then do{
                          loop_update_action s i h;
                          dnfp_mon n
                         }
                       else skip
                      )}"

definition init_env:: "nat list \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

definition init_state_env:: "nat list \<Rightarrow> (env, unit) state" where
  "init_state_env l \<equiv> State (\<lambda>x. ((),init_env l))"

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env [2,1,0]))\<close>

value \<open>sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0]))))\<close>

section\<open>Definiton of all the Pre and postconditions\<close>

subsection\<open>The invariants are taken from https://en.wikipedia.org/wiki/Dutch_national_flag_problem\<close>
definition low_invariant_is_0 where
"low_invariant_is_0 arr l\<equiv> (\<forall>x. x < l \<longrightarrow> arr!x = 0)"

definition invariant_low_to_j_is_1 where
"invariant_low_to_j_is_1 arr l j \<equiv> (\<forall>x. (x \<ge> l \<and> x < j) \<longrightarrow> arr!x = 1)"

definition high_invariant_is_2 where
"high_invariant_is_2 arr h\<equiv> (\<forall>x. x \<ge> h \<longrightarrow> arr!x = 2)"

definition invariants where
"invariants arr l j h\<equiv> low_invariant_is_0 arr l
              \<and> invariant_low_to_j_is_1 arr l j
              \<and> high_invariant_is_2 arr h"

definition invariants1 where
"invariants1 arr l j h\<equiv> low_invariant_is_0 arr l
              \<and> high_invariant_is_2 arr h"

text\<open>This can be used in the other pre and post-conditions for the methods inside loop_update_actions\<close>

text\<open>Should I just take the environment as a single parameter here?\<close>

subsection\<open>Pre- and Postconditions\<close>
definition loop_update_action_pre where
"loop_update_action_pre l j n e \<equiv> length l \<ge> Suc n \<and> 
                                    high e > j \<and>
                                    invariants l (low e) j (high e)"

definition loop_update_action_pre1 where
"loop_update_action_pre1 e \<equiv> high e > j \<and>
                             invariants1 l (low e) j (high e)"

definition loop_update_action_post where
"loop_update_action_post e e' \<equiv> length (xs e) = length (xs e')
                                \<and> length (xs e) = length (xs e')  
                                \<and> high e \<ge> high e'
                                \<and> low e \<le> low e'
                                \<and> i e \<le> i e'
                                \<and> high e - i e > high e' - i e' 
                                \<and> invariants (xs e) (low e) (i e) (high e) \<comment> \<open>This is probably not necessary\<close>
                                \<and> invariants (xs e') (low e') (i e') (high e')"

definition inc_lowbound_pre where 
"inc_lowbound_pre l j e n \<equiv> loop_update_action_pre l j n e 
                            \<and> l!j < 1"

definition dec_highbound_pre where 
"dec_highbound_pre l j e n \<equiv> loop_update_action_pre l j n e  
                              \<and> l!j > 1"

definition inc_index_pre where 
"inc_index_pre l j e n \<equiv> loop_update_action_pre l j n e  
                              \<and> l!j = 1"

definition add_high_pre where 
"add_high_pre l j e n \<equiv> loop_update_action_pre l j n e  
                              \<and> l!j > 1"

definition inc_index_pre1 where 
"inc_index_pre1 l j e n \<equiv> loop_update_action_pre1 l j n e  
                              \<and> l!j = 1"

definition inc_lowbound_post where 
"inc_lowbound_post e e'\<equiv> high e = high e'
                          \<and> low e < low e'
                          \<and> i e < i e'
                          \<and> invariants (xs e') (low e') (i e') (high e')"

definition dec_highbound_post where 
"dec_highbound_post e e' \<equiv> length (xs e) > high e' 
                              \<and> high e > high e' 
                              \<and> low e = low e'
                              \<and> i e = i e'
                              \<and> invariants (xs e') (low e') (i e') (high e')"

definition add_high_post where 
"add_high_post e e' \<equiv> high e = high e' 
                       \<and> low e = low e'
                       \<and> i e = i e'
                       \<and> length (xs e) = length (xs e')
                       \<and> invariants (xs e') (low e') (i e') (high e')"

definition inc_index_post where 
"inc_index_post e e' \<equiv> high e = high e' 
                       \<and> low e = low e'
                       \<and> i e < i e'
                       \<and> invariants (xs e') (low e') (i e') (high e')"

definition inc_index_post1 where 
"inc_index_post1 e e' \<equiv> high e = high e' 
                       \<and> low e = low e'
                       \<and> i e < i e'
                       \<and> invariants1 (xs e') (low e') (i e') (high e')"

section\<open>Simple pre- and post conditions\<close>


definition dec_highbound_simple_pre where
"dec_highbound_simple_pre l j h \<equiv> h < length l
                                    \<and> j < h  
                                    \<and> l!j > 1"
definition dec_highbound_simple_post where 
"dec_highbound_simple_post e e' \<equiv> length (xs e) > high e' 
                              \<and> high e > high e' 
                              \<and> low e = low e'
                              \<and> i e = i e' 
                              \<and> length (xs e) = length (xs e')"


definition inc_lowbound_simple_pre where 
"inc_lowbound_simple_pre l j h \<equiv> h < length l
                                    \<and> j < h  
                                    \<and> l!j < 1"

definition inc_lowbound_simple_post where 
"inc_lowbound_simple_post e e' \<equiv> length (xs e) > high e' 
                              \<and> high e = high e' 
                              \<and> low e < low e'
                              \<and> i e < i e' 
                              \<and> high e - i e > high e' - i e' 
                              \<and> length (xs e) = length (xs e')"


text\<open>This is a very simple precondition of index_j. It does not contain any invariants\<close>
definition inc_index_simple_pre where
"inc_index_simple_pre j h \<equiv> j < h"

definition inc_index_post_simple where 
"inc_index_post_simple e e' \<equiv> high e = high e' 
                       \<and> low e = low e'
                       \<and> i e < i e'
                       \<and> high e - i e > high e' - i e' 
                       \<and> xs e = xs e'"

lemma inc_lowbound_simple: "\<lbrakk>inc_lowbound_simple_pre l j1 h \<and> l = xs e \<and> i e = j1 \<and> high e = h \<and> snd(run_state (inc_lowbound l j1) e) = e2\<rbrakk> \<Longrightarrow> inc_lowbound_simple_post e e2"
  apply(simp_all add: inc_lowbound_simple_pre_def snd_def inc_lowbound_def get_low_def put_i_def put_xs_def set_xs_def put_low_def return_def get_def put_def set_low_def set_i_def inc_lowbound_simple_post_def)
  apply(simp_all add: swap_def)
  by (auto)

lemma dec_highbound_simple: "\<lbrakk>dec_highbound_simple_pre l j1 h \<and> l = xs e \<and> i e = j1 \<and> high e = h \<and> snd(run_state (dec_highbound l j1 h) e) = e2\<rbrakk> \<Longrightarrow> dec_highbound_simple_post e e2"
  apply(simp_all add: dec_highbound_simple_pre_def snd_def dec_highbound_def put_high_def put_xs_def put_def set_i_def dec_highbound_simple_post_def swap_def get_def)
  apply(simp_all add: set_high_def set_xs_def add_high_def swap_def put_xs_def get_def put_def)
  by (auto)

text\<open>This goes through pretty easy\<close>
lemma inc_index_j_simple: "\<lbrakk>inc_index_simple_pre j1 h \<and> i e = j1 \<and> high e = h \<and> snd(run_state (inc_index j1) e) = e2\<rbrakk> \<Longrightarrow> inc_index_post_simple e e2"
  apply(simp_all add: inc_index_simple_pre_def snd_def inc_index_def put_i_def put_def set_i_def inc_index_post_simple_def get_def)
  by (auto)

lemma inv_aux: "\<lbrakk>xs e = xs e2; low e = low e2; i e < i e2; high e = high2; low_invariant_is_0 (xs e) (low e)\<rbrakk> \<Longrightarrow> low_invariant_is_0 (xs e2) (low e2)"
  by(simp)

text\<open>This is the same as above, but it contains the invariants that includes some universal quantifier\<close>
lemma inc_index_j_simple_aux: "\<lbrakk>inc_index_simple_pre j1 h; i e = j1 ; high e = h; low_invariant_is_0 (xs e) (low e); 
     high_invariant_is_2 (xs e) (high e); invariant_low_to_j_is_1 (xs e) (low e) (i e);
     snd(run_state (inc_index j1) e) = e2 \<rbrakk> \<Longrightarrow> inc_index_post_simple e e2 \<Longrightarrow> low_invariant_is_0 (xs e2) (low e2) \<Longrightarrow> high_invariant_is_2 (xs e2) (high e2)"
  by(simp_all add: inc_index_simple_pre_def snd_def inc_index_def put_i_def put_def set_i_def inc_index_post_simple_def get_def)

lemma inc_index_j: "\<lbrakk>inc_index_pre1 l j e n; xs e = l; i e = j; snd(run_state (inc_index j) e) = e2\<rbrakk> \<Longrightarrow> inc_index_post1 e e2"
  apply(simp_all add: snd_def  inc_index_def inc_index_post1_def inc_index_pre1_def loop_update_action_pre1_def)
  apply(simp_all add: invariants1_def low_invariant_is_0_def high_invariant_is_2_def put_i_def get_def set_i_def put_def)
  by (auto)

text\<open>This is the proof of Inc Index that it preserves the invariants\<close>
lemma inc_index_j_real: "\<lbrakk>inc_index_pre l j e n; xs e = l; i e = j; snd(run_state (inc_index j) e) = e2\<rbrakk> \<Longrightarrow> inc_index_post e e2"
  apply(simp_all add: snd_def  inc_index_def inc_index_post_def inc_index_pre_def loop_update_action_pre_def)
  apply(simp_all add: invariants_def low_invariant_is_0_def invariant_low_to_j_is_1_def high_invariant_is_2_def put_i_def get_def set_i_def put_def)
  using less_Suc_eq by (force)

lemma add_high_keep_invariants :"\<lbrakk>add_high_pre l j e n; xs e = l; l!j = 2; i e = j; high e = h; snd(run_state (add_high l j h) e) = e2\<rbrakk> \<Longrightarrow> add_high_post e e2"
  apply(simp_all add: add_high_pre_def loop_update_action_pre_def invariants_def add_high_post_def add_high_def snd_def)
  apply(simp_all add: put_xs_def put_def get_def set_xs_def swap_def)
proof -
assume a1: "Suc n \<le> length l \<and> j < h \<and> low_invariant_is_0 l (low e) \<and> invariant_low_to_j_is_1 l (low e) j \<and> high_invariant_is_2 l h"
assume a2: "l ! j = 2"
  assume a3: "\<lparr>high = h, low = low e, i = j, xs = if j < length l \<and> h < length l then l[j := l ! h, h := l ! j] else l\<rparr> = e2"
  then have "(if j < length l \<and> h < length l then l[j := l ! h, h := 2] else l) = xs e2"
    using a2 by fastforce
  then show "h = high e2 \<and> low e = low e2 \<and> j = i e2 \<and> length l = length (xs e2) \<and> low_invariant_is_0 (xs e2) (low e2) \<and> invariant_low_to_j_is_1 (xs e2) (low e2) (i e2) \<and> high_invariant_is_2 (xs e2) (high e2)"
    using a3 a2 a1 by (metis high_invariant_is_2_def le_refl list_update_id select_convs(1) select_convs(2) select_convs(3))
qed

lemma dec_highbound: "\<lbrakk>dec_highbound_pre l j e n; l = xs e;i e = j; l!j = 2;high e = h; h < length (xs e) ;snd(run_state (dec_highbound l j h) e) = e2\<rbrakk>
                       \<Longrightarrow>  h = (Suc (high e2)) \<Longrightarrow> dec_highbound_post e e2"
  apply(simp_all add: dec_highbound_pre_def snd_def dec_highbound_def loop_update_action_pre_def invariants_def dec_highbound_post_def)
  apply(simp_all add: put_xs_def put_high_def get_def put_def set_xs_def swap_def set_high_def)
  apply(simp_all add: low_invariant_is_0_def invariant_low_to_j_is_1_def high_invariant_is_2_def add_high_def)
  apply(simp_all add: swap_def put_xs_def get_def put_def set_xs_def)
  sledgehammer

lemma inc_lowbound_post:
"\<lbrakk>inc_lowbound_pre l j e n; xs e = l; i e = j; snd (run_state (inc_lowbound l j) e) = e2\<rbrakk> \<Longrightarrow> inc_lowbound_post e e2"
  apply(simp_all add: inc_lowbound_pre_def loop_update_action_pre_def  get_low_def inc_lowbound_post_def)
  apply(simp_all add: inc_lowbound_def invariants_def  invariant_low_to_j_is_1_def low_invariant_is_0_def high_invariant_is_2_def)
  apply(simp_all add: swap_def get_low_def return_def get_def  put_xs_def fst_def snd_def)
  apply(simp_all add: put_def snd_def put_i_def get_def set_i_def set_xs_def put_low_def set_low_def)
  by(auto)

lemma inc_lowbound_post1:
"\<lbrakk>inc_lowbound_pre l j1 e n; xs e = l; i e = j1; high e = h1;
    h1 > j1; l!j1 < 1 ; snd (run_state (inc_lowbound l j1) e) = e2; high e2 = h2; i e2 = j2\<rbrakk> \<Longrightarrow> (h2 - j2) \<le> (h1 - j1) \<Longrightarrow> h2 = h1 \<Longrightarrow> j2 > j1"
  apply(simp_all add: snd_def inc_lowbound_def get_low_def return_def swap_def put_i_def put_def)
  apply(simp_all add: put_low_def set_i_def set_low_def get_def put_def put_xs_def set_xs_def)
  by (auto)

lemma inc_lowbound_post2:
"\<lbrakk>inc_lowbound_pre l j1 e n; xs e = l; i e = j1; high e = h1;
    h1 > j1; l!j1 = 0 ; snd (run_state (inc_lowbound l j1) e) = e2\<rbrakk> \<Longrightarrow> high e = high e2 \<Longrightarrow>  j2 > j1  \<Longrightarrow> inc_lowbound_post e e2"
  apply(simp_all add: snd_def inc_lowbound_def loop_update_action_pre_def  get_low_def return_def swap_def put_i_def put_def  inc_lowbound_pre_def inc_lowbound_post_def invariants_def)
  apply(simp_all add:  low_invariant_is_0_def invariant_low_to_j_is_1_def high_invariant_is_2_def  put_low_def set_i_def set_low_def get_def put_def put_xs_def set_xs_def inc_lowbound_post1)
  sorry


text\<open>The difference between high and i will never increase and will be decreased by loop_update_action\<close>
lemma termination_loop_update_action:
"\<lbrakk>init_env l = e; high e = h1; i e = j1; h1 > j1 ; snd (run_state (loop_update_action l j1 h1) e) = e2; high e2 = h2; i e2 = j2\<rbrakk> \<Longrightarrow> (h2 - j2) \<le> (h1 - j1)"
  apply(simp_all add: snd_def init_env_def loop_update_action_def)
  apply(simp_all only: inc_lowbound_def dec_highbound_def inc_index_def)
  apply(simp_all only: get_low_def put_xs_def get_def put_def put_i_def set_xs_def set_i_def put_low_def set_low_def put_high_def)
  apply(simp_all only: swap_def set_high_def dec_highbound_simple inc_lowbound_simple inc_index_j_simple)
  sledgehammer
  sorry


lemma termination_loop_update_action:
"\<lbrakk>init_env l = e; high e = h1; i e = j1; h1 > j1 ; h1 - j1 = dif1; snd (run_state (loop_update_action l j1 h1) e) = e2; high e2 = h2; i e2 = j2\<rbrakk> \<Longrightarrow> (h2 - j2) < (h1 - j1) "



text\<open>Would you add your condition to the assumptions?
     I mean would you extract low and make sure all elements before low are 0?\<close>
lemma low_and_down_is_0:
"\<lbrakk>init_env l = e;  low e = l1; \<forall>x:: nat. x < l1 \<Longrightarrow> l!x = 0; l!j = 0; low(snd (run_state (inc_lowbound l j) e)) = l2\<rbrakk> \<Longrightarrow> l1 < l2 "
  sorry

lemma low_to_i_is_1:
"\<lbrakk>dfs1_dfs_dom (Inl (x, e)); black e = bl1; black (snd (run_state (dfs1 x) e)) = bl2 \<rbrakk> \<Longrightarrow> bl1 \<subseteq> bl2"
  sorry

lemma i_to_high_is_nonsorted:
"\<lbrakk>dfs1_dfs_dom (Inl (x, e)); black e = bl1; black (snd (run_state (dfs1 x) e)) = bl2 \<rbrakk> \<Longrightarrow> bl1 \<subseteq> bl2"
  sorry

lemma high_and_up_is_2:
"\<lbrakk>dfs1_dfs_dom (Inl (x, e)); black e = bl1; black (snd (run_state (dfs1 x) e)) = bl2 \<rbrakk> \<Longrightarrow> bl1 \<subseteq> bl2"
  sorry

lemma length_dnfp: "length(dnfp n xs k j k) = length xs"
  apply(induction n)
   apply(simp)
    apply(simp add: swap_def length_swap)
  apply(simp)
  sorry

lemma distinct_dnfp[simp]:
  "distinct(dnfp n xs k j k) = distinct xs"
  apply(induction n)
   apply(simp)
   apply(simp add: swap_def)
  sorry

fun dnfp_alt:: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp_alt [] s _ _ _ _ = s"|
"dnfp_alt (x#xs) s low high i mid = (if high > i then (if s!i < mid then (dnfp_alt xs (swap s i low) (Suc low) high (Suc i) mid)
                                      else (if s!i > mid then (dnfp_alt xs (swap s i (high-1)) low (high-1) i mid)
                                       else (dnfp_alt xs s low high (Suc i) mid))) else s)"


text\<open>How do I evaluate this - where I define a variable/constant and use it in a function call\<close>
value\<open>(xs = [0,0,2,2,1] \<Longrightarrow> (dnfp (length xs) xs 0 (length xs) 1 = [0,0,1,2,2]))\<close>


value\<open>(dnfp 5 [0,0,2,2,1] 0 5 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1)\<close>
value\<open>sorted(dnfp 7 [1,0,2,0,2,2,1] 0 7 1 )\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1 )\<close>
value\<open>(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1)\<close>

value\<open>(dnfp1 5 [0,0,2,2,1] 0 5 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp1 8 [1,0,2,0,2,0,2,1] 0 8 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>sorted(dnfp1 8 [1,0,2,0,2,0,2,1] 0 8 1)\<close>
value\<open>sorted(dnfp1 7 [1,0,2,0,2,2,1] 0 7 1 )\<close>
value\<open>sorted(dnfp1 8 [1,0,2,0,2,2,1,0] 0 8 1 )\<close>
value\<open>(dnfp1 8 [1,0,2,0,2,2,1,0] 0 8 1)\<close>


end