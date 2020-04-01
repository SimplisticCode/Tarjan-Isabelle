theory Dutch_National_Flag_Monad
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin

text\<open>Monad definitions to encode and extract data from the monad\<close>

record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat list"
  
definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(env, env) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "env \<Rightarrow> (env, unit) state" where "put x = State (\<lambda>_. ((),x))"

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

text\<open>The algorithm is constant so n is originally defined as the size of the list.
      s is the list I am sorting
      low is the bound of sorted array
      i is the current element being investigated\<close>
fun dnfp:: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp 0 s _ _ _ = s"|
"dnfp (Suc 0) s _ _ _ = s"|
"dnfp (Suc n) s l h j = (if h > j then (if s!j < 1 then (dnfp n (swap s j l) (Suc l) h (Suc j))
                                else (if s!j > 1 then (dnfp n (swap s j (h-1)) l (h-1) j)
                                  else (dnfp n s l h (Suc j))))
                             else s)"

text\<open>Is this better - with the let and (Suc high)?\<close>
fun dnfp1:: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp1 0 s _ _ _ = s"|
"dnfp1 (Suc 0) s _ _ _ = s"|
"dnfp1 (Suc n) s l (Suc h) j = (if (Suc h) > j then (
                                  let (xs, l1, h1, j1) = (if s!j < 1 then ((swap s j l), (Suc l), (Suc h), (Suc j))
                                                 else (if s!j > 1 then ((swap s j h), l, h, j)
                                                 else (s, l, (Suc h), (Suc j))))
                                  in (dnfp1 n xs l1 h1 j1))
                             else s)"

text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
fun dnfp_mon:: "nat \<Rightarrow> (env, unit) state" where
"dnfp_mon 0  = skip"|
"dnfp_mon (Suc 0)  = skip"|
"dnfp_mon (Suc n)  = do{
                        h \<leftarrow> get_high;
                        i \<leftarrow> get_i;
                        s \<leftarrow> get_xs;
                        (if h > i then
                                do{
                                  (if s!i < 1 then do {
                                            l \<leftarrow> get_low;                                       
                                            put_xs (swap s i l);
                                            put_i (Suc i);
                                            put_low (Suc l);
                                            dnfp_mon n
                                          }
                                   else (if s!i > 1 then do
                                          {
                                            put_high (h - 1);
                                            put_xs (swap s i (h-1));
                                            dnfp_mon n
                                          }
                                       else do {
                                         put_i (Suc i);
                                        dnfp_mon n
                                       }))
                                }
                             else skip)
                      }"

definition init_env:: "nat list \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>high = (length l),            low = 0,
                 i = 0,                         xs = l\<rparr>"

definition init_state_env:: "nat list \<Rightarrow> (env, unit) state" where
  "init_state_env l \<equiv> State (\<lambda>x. ((),init_env l))"

value \<open>snd(run_state (dnfp_mon 5) (init_env [0,2,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 9) (init_env [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>snd(run_state (dnfp_mon 3)(init_env[2,1,0]))\<close>

value \<open>sorted(xs(snd(run_state (dnfp_mon 5) (init_env[0,2,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 9) (init_env[0,2,2,0,1,0,2,1,2]))))\<close>
value \<open>sorted(xs(snd(run_state (dnfp_mon 3) (init_env[2,1,0]))))\<close>


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