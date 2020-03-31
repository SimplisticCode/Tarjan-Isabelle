theory Int_Pair_State_Fib
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

(*
definition return:: "nat \<Rightarrow> ('b, nat) state" where "return = State_Monad.return"
definition get:: "(nat pair, nat pair) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "nat pair \<Rightarrow> (nat pair, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition get_fst:: "(nat pair, nat) state" where "get_fst = do { x \<leftarrow> get; return (fst x) }"
definition get_snd:: "(nat pair, nat) state" where "get_snd = do { x \<leftarrow> get; return (snd x) }"
definition set_fst:: "nat pair \<Rightarrow> nat \<Rightarrow> nat pair" where "set_fst v x = (x, snd v)"
definition set_snd:: "nat pair \<Rightarrow> nat \<Rightarrow> nat pair" where "set_snd v x = (fst v, x)"
definition put_fst:: "nat \<Rightarrow> (nat pair, unit) state" where "put_fst x = do { v \<leftarrow> get; put (set_fst v x) }"
definition put_snd:: "nat \<Rightarrow> (nat pair, unit) state" where "put_snd x = do { v \<leftarrow> get; put (set_snd v x) }"
definition skip:: "(nat pair, unit) state" where "skip = State (\<lambda>x. ((),x))"
*)

fun fibacc :: "nat \<Rightarrow> nat => nat \<Rightarrow> nat" where
fa1: "fibacc 0 a b = a"| 
fa2: "fibacc (Suc 0) a b = b"|
fa3: "fibacc (Suc (Suc n)) a b = fibacc (Suc n) b (a+b)"

definition fib_wrap:: "nat \<Rightarrow> nat" where
"fib_wrap n = fibacc n 0 1"

fun fib :: "nat => nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"

text\<open>Experiment with finding a pattern to extract in the proof\<close>
value \<open>fibacc 2 (fib 7) (fib 8)\<close>
value \<open>fibacc 8 (fib 1) (fib 2)\<close>
value \<open>fibacc 6 (fib 1) (fib 2)\<close>
value \<open>fib 5 + fibacc (Suc 5) 0 1 = fib 7\<close>
value \<open>fibacc (Suc 5) 0 (fibacc 5 0 1) = fibacc (Suc( Suc 5)) 0 1\<close>
value \<open>fibacc (Suc 5) 0 1 =  fibacc (Suc (Suc 5)) 0 1 - fibacc 5 0 1\<close>
value \<open>fibacc 5 0 (fibacc 5 0 1)\<close>
value \<open>fibacc 5 (fib 1) (fib 2)\<close>
value\<open>fib 7\<close>

lemma fib_aux: "fibacc n b (a + b) = fibacc (Suc n) a b"
  apply(induction n)
   apply(simp_all)
  done

lemma fib_aux1: "fibacc (Suc (Suc n)) a b = fibacc n a b + fibacc (Suc n) a b"
  apply(induct n arbitrary: a b)
  apply(simp_all)
  apply(simp only: fib_aux)
  done

lemma fib_main1: "fib n = fibacc n 0 1"
  apply(induction n rule: fib.induct)
    apply(simp)
    apply(simp)
    apply (simp only: fib_aux1)
  by (simp)

lemma fibwrap_main: "fib_wrap n = fibacc n 0 1"
  apply(induction n rule: nat.induct)
   apply(simp_all add: fib_wrap_def)
  done

lemma fib_main: "fib_wrap n = fib n"
  apply(induction n rule: fib.induct)
   apply(simp_all add: fib_main1 fibwrap_main)
  done

text\<open>The fibonacci function does always return the result at the fst value of the pair. The initial state passed in should be (0,1)\<close>
fun monfib:: "nat \<Rightarrow> (nat pair, unit) state" where
  "monfib 0 = skip" |
  "monfib (Suc 0) = do {b \<leftarrow> get_snd; put_fst b}" |
  "monfib (Suc (Suc n)) = do { a \<leftarrow> get_fst; b \<leftarrow> get_snd; put (b,(a + b)); monfib (Suc n)}"

text\<open>Stefan do you - know why I can't run any of these examples?\<close>
value \<open>fst(snd(run_state (monfib 5) (fst((0,1), ()))))\<close>
value \<open>fst(snd(run_state (monfib 5) (0,1)))\<close>

value "fst(snd (run_state (monfib 6) x))"

lemma monfib_aux: "fst(snd (run_state (monfib n) (b, (a + b)))) = fst(snd (run_state (monfib (Suc n)) (a, b)))"
  apply(induction n rule: nat.induct)
   apply(simp_all add: skip_def snd_def fst_def get_fst_def get_snd_def put_def put_fst_def get_def return_def set_fst_def)
  done

value "fst(snd (run_state (monfib (Suc (Suc 4))) x)) 
        = fst(snd (run_state (monfib 4) x)) + fst(snd (run_state (monfib (Suc 4)) x))"

lemma monfib_aux1: "fst(snd (run_state (monfib (Suc (Suc n))) x)) 
      = fst(snd (run_state (monfib n) x)) + fst(snd (run_state (monfib (Suc n)) x))"
  apply (induction n arbitrary: x rule: nat.induct)
   apply (simp_all add: skip_def get_snd_def return_def snd_def get_def put_fst_def set_fst_def put_def get_fst_def fst_def)
  by (simp add: case_prod_beta' monfib_aux)

lemma fib_mon_basic: "fst(snd(run_state (monfib n) (a,b))) = fibacc n a b"
  apply (induction n arbitrary: a b)
  apply(simp_all add: skip_def snd_def fst_def get_fst_def get_snd_def put_def put_fst_def)
  by (metis case_prod_beta' fib_aux monfib_aux)

lemma fib_m_main: "fst(snd(run_state (monfib n) (0,1))) = fib n"
  apply (induction n rule:fib.induct)
  apply(simp_all add: skip_def snd_def fst_def get_fst_def get_snd_def put_def put_fst_def get_def return_def set_fst_def)
  by (metis One_nat_def add.commute case_prod_beta' monfib_aux monfib_aux1 plus_1_eq_Suc)

lemma fib_basic_aux: "fst(snd(run_state (monfib n) (0,1))) = fibacc n 0 1"
apply (induction n)
apply(simp_all add: skip_def snd_def fst_def)
  by (metis One_nat_def case_prod_beta' fib_m_main fib_main1)

end