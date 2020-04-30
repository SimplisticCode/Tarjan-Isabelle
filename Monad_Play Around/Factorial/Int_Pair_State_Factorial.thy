theory Int_Pair_State_Factorial
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

fun monfact:: "nat \<Rightarrow> (nat pair, unit) state" where
mf1: "monfact 0 = skip" |
mf2: "monfact (Suc n) = do { y \<leftarrow> get_fst; y \<leftarrow> return (y * (Suc n)); put_fst y; monfact n }"

value \<open>fst(snd (run_state (monfact 5) (1,x)))\<close>

lemma monfact_mult: "fst(snd (run_state (monfact n) (a * b, y))) =  b * fst(snd (run_state (monfact n) (a, y)))"
  apply (induction n arbitrary: a b)
  apply (simp add: skip_def)
  apply (simp add: return_def put_def get_def)
  by (metis mult.assoc mult.commute mult_Suc)
  
lemma monfact_shift: "fst(snd (run_state (monfact (Suc n)) (x,y))) = fst(snd (run_state (monfact n) ((Suc n) * x, y)))"
  apply (induction n arbitrary: x)
  apply (simp add: get_fst_def put_fst_def return_def)
   apply (simp add: put_fst_def return_def get_def fst_def snd_def)
  sledgehammer
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
  using Int_Pair_State_Factorial.af2 accfact_mult by presburger


value "fst(snd (run_state (monfact 6) (1::nat, y::nat)))"
value "accfact 6 (fst(1::nat, y::nat))"

text\<open>Stefan - Need a hint for this one. Should I use some other lemmas?\<close>
lemma fact_basic: "fst(snd (run_state (monfact n) x)) = accfact n (fst(x))"
  apply (induction n arbitrary: x)
   apply (simp add: skip_def )
    apply(simp add: put_fst_def fst_def snd_def get_fst_def return_def)
      using accfact_aux monfact_aux sledgehammer
end