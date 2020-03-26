theory Int_State_Monad_Fib
imports 
  Main
  "~~/src/HOL/Library/State_Monad"
begin

definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(nat, nat) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "nat \<Rightarrow> (nat, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition skip:: "(nat, unit) state" where "skip = State (\<lambda>x. ((),x))"

fun fibacc :: "nat \<Rightarrow> nat => nat \<Rightarrow> nat" where
fa1: "fibacc 0 a b = a"| 
fa2: "fibacc (Suc 0) a b = b"| 
fa3: "fibacc (Suc (Suc n)) a b = fibacc (Suc n) b (a+b)"

definition fib_wrap:: "nat \<Rightarrow> nat" where
  "fib_wrap n \<equiv> fibacc n 1 1"

fun monfibacc :: "nat \<Rightarrow> nat => (nat, unit) state" where
m1:  "monfibacc 0 a = skip"| 
m2:  "monfibacc (Suc n) a  = do{b \<leftarrow> get; put (a + b); monfibacc n b}"

definition monfib_wrap where
  "monfib_wrap n \<equiv> (monfibacc n 1)"

value \<open>fibacc 9 1 1 = 55\<close>
value \<open>snd (run_state (monfibacc 9 0) (1::nat)) = 55\<close>
value \<open>fib_wrap 9 = 55\<close>
value \<open>snd (run_state (monfib_wrap 9) (1::nat))\<close>
value \<open>snd (run_state (monfib_wrap 2) (0::nat))\<close>
value \<open>snd (run_state (monfib_wrap 0) (snd (run_state (monfib_wrap 7) 1)))\<close>
value \<open>snd (run_state (monfib_wrap 7) 1)\<close>

lemma fib_base[simp]: "snd (run_state (monfib_wrap 0) (Suc 0)) = fib_wrap 0"
  by (simp add: fib_wrap_def monfib_wrap_def put_def skip_def)

lemma fib_wrap_aux[simp]: "fib_wrap (Suc (Suc n)) = fib_wrap n + fib_wrap (Suc n)"
  apply (induction n)
   apply (simp add: fib_wrap_def)
  sledgehammer
  using Int_State_Monad.fa3 fib_wrap_def
  sorry


lemma monfib_aux[simp]: "snd (run_state (monfib_wrap (Suc (Suc n))) x) 
        = snd (run_state (monfib_wrap (Suc n)) x) + snd (run_state (monfib_wrap n) x)"
  apply (induction n arbitrary: x)
   apply(simp_all)

  sorry

lemma monfib_aux[simp]: "snd (run_state (monfib_wrap (Suc (Suc n))) x) 
        = snd (run_state (monfib_wrap (Suc n)) (snd (run_state (monfib_wrap n) x)))"
  apply (induction n arbitrary: x)
  sledgehammer
   apply (simp add: put_def snd_def get_def skip_def)
  sledgehammer
  sorry

lemma fib_basic: "snd (run_state (monfib_wrap n) 1) = fib_wrap n"
  apply (induction n)
   apply (simp)
  sorry


end