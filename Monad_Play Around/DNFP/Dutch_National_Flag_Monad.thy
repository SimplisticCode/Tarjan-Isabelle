theory Dutch_National_Flag_Monad
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin

text\<open>Monad definitions to encode and extract data from the monad\<close>
datatype color = red | white | blue

record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat list"
  
definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(env, env) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "env \<Rightarrow> (env, unit) state" where "put x = State (\<lambda>_. ((),x))"
text\<open>Ask Stefan about how to do generic get\<close>
definition get_gen:: "char list\<Rightarrow> (env, 'a) state" where "get_gen acc = do { x \<leftarrow> get; return (acc  x)}"

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


definition swap:: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
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

definition dec_highbound where
"dec_highbound s j h\<equiv> do{
                    put_high (h - 1);
                    put_xs (swap s j (h-1))
                }"

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
   put_i (Suc j)
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


section\<open>Pre and postconditions\<close>
definition inc_lowbound_pre where 
"inc_lowbound_pre l j e n \<equiv> init_env l = e \<and>
                             length l = Suc n \<and> 
                             high e > j \<and>  
                             l!j < 1"

definition dec_highbound_pre where 
"dec_highbound_pre l j e n \<equiv> init_env l = e \<and>
                             length l = Suc n \<and>
                             high e > j \<and>  
                             l!j > 1"

definition inc_lowbound_post where 
"inc_lowbound_post e e'\<equiv> high e = high e' \<and>
                          low e < low e' \<and>
                          i e < i e' \<and>
                          (\<forall>x. x < low e' \<longrightarrow> (xs e')!x = 1) \<and>
                            high e - i e > high e' - i e' \<and>
                            length (xs e) = length (xs e') \<and>
                            distinct (xs e) = distinct (xs e')"

definition dec_highbound_post where 
"dec_highbound_post l e e' \<equiv> init_env l = e \<and>
                                length l > high e' \<and>
                                (\<forall>x. x > high e' \<longrightarrow> (xs e')!x = 2) \<and>
                                high e - i e > high e' - i e' \<and>
                                length (xs e) = length (xs e') \<and>
                                distinct (xs e) = distinct (xs e')"

lemma inc_lowbound_post:
"\<lbrakk>init_env l = e; length l = Suc n; low e = l1; i e = j1; high e = h1; 
    h1 > j1; l!j1 < 1 ; snd (run_state (inc_lowbound l j1) e) = e2; high e2 = h2; i e2 = j2\<rbrakk> \<Longrightarrow> (h2 - j2) \<le> (h1 - j1)"
  apply(simp_all add: snd_def inc_lowbound_def get_low_def return_def swap_def put_i_def put_def)
  apply(simp_all add: put_low_def set_i_def set_low_def get_def put_def put_xs_def set_xs_def)
  apply(simp_all add: low_def Record.iso_tuple_snd_def Record.iso_tuple_fst_def fst_def env_ext_Tuple_Iso_def Record.tuple_iso_tuple_def snd_def)
  apply(simp add: init_env_def low_def high_def Record.iso_tuple_fst_def fst_def Record.tuple_iso_tuple_def env_ext_Tuple_Iso_def)
   apply(simp_all only: repr_def iso_tuple_snd_def low_def high_def Record.iso_tuple_fst_def fst_def Record.tuple_iso_tuple_def env_ext_Tuple_Iso_def)
  apply(simp_all add: id_def)
  sledgehammer
  sorry


text\<open>The difference between high and i will never increase and will be decreased by loop_update_action\<close>
lemma termination_loop_update_action:
"\<lbrakk>init_env l = e; length l = Suc n; high e = h1; i e = j1; h1 > j1 ; snd (run_state (loop_update_action l j1 h1) e) = e2; high e2 = h2; i e2 = j2\<rbrakk> \<Longrightarrow> (h2 - j2) \<le> (h1 - j1)"
  apply(simp_all add: snd_def high_def init_env_def i_def Record.iso_tuple_fst_def Record.tuple_iso_tuple_def fst_def Record.iso_tuple_snd_def)
   apply(simp_all add: Record.repr_def env_ext_Tuple_Iso_def)
  apply(simp_all add: loop_update_action_def inc_lowbound_def inc_lowbound_post dec_highbound_def put_i_def)
   apply(simp only: loop_update_action_def inc_lowbound_def dec_highbound_def put_i_def)
   apply(simp only: put_xs_def get_def get_low_def get_high_def put_def return_def put_low_def set_i_def set_xs_def put_high_def)
  apply(simp only: set_low_def swap_def return_def set_high_def high_def low_def )
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