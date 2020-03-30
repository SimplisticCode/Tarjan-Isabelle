theory Int_State_Monad
imports 
  Main
  "~~/src/HOL/Library/State_Monad"
begin

definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(nat, nat) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "nat \<Rightarrow> (nat, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition skip:: "(nat, unit) state" where "skip = State (\<lambda>x. ((),x))"

lemma monad_example1: "fst(run_state (do { return 1 }) 2) = 1" 
  by (simp add: return_def)

lemma monad_example2: "fst(run_state (do { put 1; x \<leftarrow> get; return x }) 2) = 1"
  by (simp add: get_def put_def return_def)

lemma monad_example3: "snd(run_state (do { put 1; x \<leftarrow> get; return x }) 2) = 1"
  by (simp add: get_def put_def return_def)

lemma monad_example4: 
"fst((run_state (do { x \<leftarrow> return 1; put x; return x })::(nat \<Rightarrow> nat \<times> nat)) 2) = 1"
  by (simp add: put_def return_def)

lemma monad_example5: "snd((run_state (do { x \<leftarrow> return 1; put x })::(nat \<Rightarrow> unit \<times> nat)) 2) = 1"
  by (simp add: put_def return_def)

definition prog:: "(nat, nat) state" 
  where "prog = do { a \<leftarrow> get; b \<leftarrow> return (a + 1); put b; return b }"

definition init_prog:: "(nat, nat) state" where "init_prog = do { put 1; prog }"

lemma monad_example6: "snd (run_state init_prog 0) = 2"
  by (simp add: init_prog_def prog_def put_def get_def return_def)

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
  using Int_State_Monad.af2 accfact_mult by presburger
  
fun monfact:: "nat \<Rightarrow> (nat, unit) state" where
mf1: "monfact 0 = skip" |
mf2: "monfact (Suc n) = do { y \<leftarrow> get; y \<leftarrow> return (y * (Suc n)); put y; monfact n }"

lemma monfact_mult: "snd (run_state (monfact n) (a * b)) = b * snd (run_state (monfact n) a)"
  apply (induction n arbitrary: a b)
  apply (simp add: skip_def)
  apply (simp add: return_def put_def get_def)
  by (metis mult.assoc mult.commute mult_Suc)
  
lemma monfact_shift: "snd (run_state (monfact (Suc n)) x) = snd (run_state (monfact n) ((Suc n) * x))"
  apply (induction n arbitrary: x)
  apply (simp add: get_def put_def return_def)
  apply (simp add: put_def return_def get_def)
  by (simp add: mult.commute)

lemma monfact_aux: "snd (run_state (monfact (Suc n)) x) = (Suc n) * snd (run_state (monfact n) x)"
  apply (induction n arbitrary: x)
   apply (simp add: skip_def return_def get_def put_def)
  by (metis monfact_mult monfact_shift mult.commute)
  
lemma fact_basic: "snd (run_state (monfact n) (x::nat)) = accfact n (x::nat)"
  apply (induction n)
   apply (simp add: put_def fst_def skip_def)
  using accfact_aux monfact_aux by auto

lemma fact_main: "snd (run_state (do { put (1::nat); monfact n }) (x::nat)) = accfact n (1::nat)"
  by (simp add: fact_basic put_def)

fun fibacc :: "nat \<Rightarrow> nat => nat \<Rightarrow> nat" where
fa1: "fibacc 0 a b = a"| 
fa2: "fibacc (Suc 0) a b = b"| 
fa3: "fibacc (Suc (Suc n)) a b = fibacc (Suc n) b (a+b)"

definition fib_wrap:: "nat \<Rightarrow> nat" where
  "fib_wrap n \<equiv> fibacc n 1 1"

fun monfibacc :: "nat \<Rightarrow> nat => (nat, unit) state" where
m1:  "monfibacc 0 a = skip"| 
m3:  "monfibacc (Suc n) a  = do{b \<leftarrow> get; put (a + b); monfibacc n b}"

definition monfib_wrap where
  "monfib_wrap n \<equiv> (monfibacc n 1)"

value \<open>fibacc 9 1 1 = 55\<close>
value \<open>snd (run_state (monfibacc 9 0) (1::nat)) = 55\<close>
value \<open>fib_wrap 9 = 55\<close>
value \<open>snd (run_state (monfib_wrap 9) (1::nat))\<close>
value \<open>snd (run_state (monfib_wrap 2) (1::nat))\<close>
value \<open>snd (run_state (monfib_wrap (Suc 0)) (snd (run_state (monfib_wrap 0) 1)))\<close>
value \<open>snd (run_state (monfib_wrap (Suc (Suc 0))) 1)\<close>

lemma fib_base[simp]: "snd (run_state (monfib_wrap 0) (Suc 0)) = fib_wrap 0"
  by (simp add: fib_wrap_def monfib_wrap_def put_def skip_def)




lemma fib_basic: "snd (run_state (monfib_wrap n) 1) = fib_wrap n"
  apply (induction n)
   apply (simp)
  sorry
    

end