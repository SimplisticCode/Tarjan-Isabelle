theory Int_Pair_State_Monad
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin

type_synonym 'a pair = "'a \<times> 'a"

definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "('a pair, 'a pair) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "'a pair \<Rightarrow> ('a pair, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition get_fst:: "('a pair, 'a) state" where "get_fst = do { x \<leftarrow> get; return (fst x) }" 
definition get_snd:: "('a pair, 'a) state" where "get_snd = do { x \<leftarrow> get; return (snd x) }" 
definition set_fst:: "'a pair \<Rightarrow> 'a \<Rightarrow> 'a pair" where "set_fst v x = (x, snd v)"
definition set_snd:: "'a pair \<Rightarrow> 'a \<Rightarrow> 'a pair" where "set_snd v x = (fst v, x)"
definition put_fst:: "'a \<Rightarrow> ('a pair, unit) state" where "put_fst x = do { v \<leftarrow> get; put (set_fst v x) }"
definition put_snd:: "'a \<Rightarrow> ('a pair, unit) state" where "put_snd x = do { v \<leftarrow> get; put (set_snd v x) }"
definition skip:: "('a pair, unit) state" where "skip = State (\<lambda>x. ((),x))"


definition inject_npu:: "(nat pair, unit) state" where "inject_npu = State (\<lambda>x. ((),x))"

fun monfact:: "nat \<Rightarrow> (nat pair, unit) state" where
mf1: "monfact 0 = skip" |
mf2: "monfact (Suc n) = do { y \<leftarrow> get_fst; y \<leftarrow> return (y * (Suc n)); put_fst y; monfact n }"

fun fibacc :: "nat \<Rightarrow> nat => nat \<Rightarrow> nat" where
fa1: "fibacc 0 a b = a"| 
fa2: "fibacc (Suc 0) a b = b"|
fa3: "fibacc (Suc (Suc n)) a b = fibacc (Suc n) b (a+b)"

value \<open>fibacc 6 0 1 = 8\<close>
value \<open>fibacc 9 0 1 = 34\<close>

definition fib_wrap:: "nat \<Rightarrow> nat" where
"fib_wrap n = fibacc n 0 1"

fun fib :: "nat => nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "(fib n)*(fib (Suc (Suc n))) \<le> (fib (Suc n)) * (fib (Suc n)) + 1
              \<and> (fib (Suc n))*(fib (Suc n)) \<le> (fib n)* (fib (Suc (Suc n))) + 1"
  apply (induct_tac n)
   apply simp
  apply (simp add: right_mult_distrib left_distrib)
done

lemma [simp]: "fibacc (Suc n) 0 1 > 0"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume "fibacc n 0 1 > 0"
    from this have "fibacc (Suc n) 0 1 \<ge> fibacc n 0 1" by (simp add: fa1 fa2 fa3)
    from this and `fibacc n 0 1 > 0` show  "fibacc (Suc n) 0 1 > 0"
      using (Suc.IH) by blast
  qed

lemma [simp]: "fib (Suc n) > 0"
  by (induct n rule: fib.induct) simp_all

text {* Alternative induction rule. *}
theorem fib_induct:
    "P 0 ==> P 1 ==> (\<And>n. P (n + 1) ==> P n ==> P (n + 2)) ==> P (n::nat)"
  by (induct rule: fib.induct) simp_all

text\<open>The fibonacci function does always return the result at the fst value of the pair. The initial state passed in should be (0,1)\<close>
fun monfib:: "nat \<Rightarrow> (nat pair, unit) state" where
  "monfib 0 = skip" |
  "monfib (Suc 0) = do {a \<leftarrow> get_snd; put_fst a}" |
  "monfib (Suc (Suc n)) = do { a \<leftarrow> get_fst; b \<leftarrow> get_snd; temp_b \<leftarrow> return b; b \<leftarrow> return (a + b); put (temp_b,b); monfib (Suc n)}"

value \<open>fst(snd(run_state (monfib 4) e))\<close>

lemma fib_add:
  "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n")
proof (induct n rule: fib_induct)
  show "?P 0" by simp
  show "?P 1" by simp
  fix n
  have "fib (n + 2 + k + 1)
    = fib (n + k + 1) + fib (n + 1 + k + 1)" by simp
  also assume "fib (n + k + 1)
    = fib (k + 1) * fib (n + 1) + fib k * fib n"
      (is " _ = ?R1")
  also assume "fib (n + 1 + k + 1)
    = fib (k + 1) * fib (n + 1 + 1) + fib k * fib (n + 1)"
      (is " _ = ?R2")
  also have "?R1 + ?R2
    = fib (k + 1) * fib (n + 2 + 1) + fib k * fib (n + 2)"
    by (simp add: add_mult_distrib2)
  finally show "?P (n + 2)" .
qed


lemma monfib_aux: "fst(snd (run_state (monfib (Suc (Suc n))) x)) = fst(snd (run_state (monfib n) x)) + fst(snd (run_state (monfib (Suc n)) x))"
  apply (induction n arbitrary: x)
   apply (simp add:  skip_def)
   apply (simp add: get_def set_fst_def)
  sledgehammer


lemma fib_basic: "fst(snd(run_state (monfib n) x)) = fibacc n ((fst x)::nat) ((snd x)::nat)"
  apply (induction n arbitrary: x)
   apply (simp add:  skip_def)
  sorry

value \<open>fst(snd (run_state (monfact 10) e))\<close>
lemma monfact_mult: "fst(snd (run_state (monfact n) (a * b, y))) =  b * fst(snd (run_state (monfact n) (a, y)))"
  apply (induction n arbitrary: a b)
  apply (simp add: skip_def)
  apply (simp add: return_def put_def get_def)
  by (metis mult.assoc mult.commute mult_Suc)
  
lemma monfact_shift: "fst(snd (run_state (monfact (Suc n)) (x,y))) = fst(snd (run_state (monfact n) ((Suc n) * x, y)))"
  apply (induction n arbitrary: x y)
  apply (simp add: get_fst_def put_fst_def return_def)
   apply (simp add: put_fst_def return_def get_def fst_def snd_def)
  sorry

lemma monfact_aux: "fst(snd (run_state (monfact (Suc n)) x)) = (Suc n) * fst(snd (run_state (monfact n) x))"
  apply (induction n arbitrary: x)
   apply (simp add: skip_def return_def get_def put_def)
  by (metis monfact_mult monfact_shift mult.commute)

fun accfact:: "nat \<Rightarrow> nat \<Rightarrow> nat" where
af1:  "accfact 0 a = a" |
af2: "accfact (Suc n) a = accfact n (a * Suc n)"

lemma accfact_mult: "accfact n (a * b) = b * accfact n a"
  apply (induction n arbitrary: a b)
   apply (simp)
  apply (simp only: af2)
  by (simp add: semiring_normalization_rules(19))

lemma accfact_aux: "accfact (Suc n) x = (Suc n) * accfact n x"
  apply (induction n)
   apply simp
  using Int_Pair_State_Monad.af2 accfact_mult by presburger


value "fst(snd (run_state (monfact 6) (1::nat, y::nat)))"
value "accfact 6 1"


lemma fact_basic: "fst(snd (run_state (monfact n) (x::nat,y::nat))) = accfact n (fst(x::nat,y::nat))"
  apply (induction n arbitrary: x y)
   apply (simp add: put_fst_def get_fst_def snd_def fst_def skip_def)
  sledgehammer


lemma monad_example1: "fst(snd(run_state (do { put (1, 1) }) (0, 0))) = 1" 
  by (simp add: put_def)

lemma monad_example2: "snd(snd(run_state (do { put (1, 1) }) (0, 0))) = 1" 
  by (simp add: put_def)

lemma monad_example3: "fst(run_state (do { put (1, 2); x \<leftarrow> get_fst; return x }) (0, 0)) = 1"
  by (simp add: get_fst_def put_def get_def return_def)

lemma monad_example4: "fst(run_state (do { put (1, 2); x \<leftarrow> get_snd; return x }) (0, 0)) = 2"
  by (simp add: get_snd_def put_def get_def return_def)

value "snd(snd((run_state (do { x \<leftarrow> return (3::nat); put_snd x })) (2, 2)))"

lemma monad_example5: "snd(snd((run_state (do { x \<leftarrow> return 1; put_snd x })) (2, 2))) = 1"
  by (simp add: put_snd_def put_def set_snd_def get_def return_def)

lemma monad_example6: "fst(snd((run_state (do { x \<leftarrow> return 1; put_snd x })) (2, 2))) = 2"
  by (simp add: put_snd_def put_def set_snd_def get_def return_def)

definition swap:: "(nat pair, unit) state" 
  where "swap = do { a \<leftarrow> get_fst; b \<leftarrow> get_snd; put_fst b; put_snd a }"

lemma monad_example7: "snd (run_state swap (x,y)) = (y,x)"
  by (simp add: swap_def put_def get_fst_def get_snd_def put_fst_def put_snd_def set_fst_def set_snd_def get_def return_def)



end