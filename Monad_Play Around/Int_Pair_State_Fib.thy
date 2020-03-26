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
  by (smt add_Suc add_mult_distrib2 eq_iff le_Suc_eq)


lemma [simp]: "fibacc (Suc n) 0 1 > 0"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    assume "fibacc n 0 1 > 0"
    from this have "fibacc (Suc n) 0 1 \<ge> fibacc n 0 1" sorry
    from this and `fibacc n 0 1 > 0` have  "fibacc (Suc n) 0 1 > 0"
      using Suc.IH by (blast)
    then show "fibacc (Suc n) 0 1 > 0" by auto
  qed

lemma [simp]: "fib (Suc n) > 0"
  by (induct n rule: fib.induct) simp_all

text {* Alternative induction rule. *}
theorem fib_induct:
    "P 0 ==> P 1 ==> (\<And>n. P (n + 1) ==> P n ==> P (n + 2)) ==> P (n::nat)"
  by (induct rule: fib.induct) simp_all

lemma fib_wrap: "fib_wrap n = fib n"
proof (induct n)
  case 0
  then show ?case 
  by (simp add: fib_wrap_def)
next
  case (Suc n)
  then show ?case 
  by slegdehammer
  sorry
qed

text\<open>The fibonacci function does always return the result at the fst value of the pair. The initial state passed in should be (0,1)\<close>
fun monfib:: "nat \<Rightarrow> (nat pair, unit) state" where
  "monfib 0 = skip" |
  "monfib (Suc 0) = do {a \<leftarrow> get_snd; put_fst a}" |
  "monfib (Suc (Suc n)) = do { a \<leftarrow> get_fst; b \<leftarrow> get_snd; temp_b \<leftarrow> return b; b \<leftarrow> return (a + b); put (temp_b,b); monfib (Suc n)}"

value \<open>fst(snd(run_state (monfib 4) x))\<close>

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


value "fst(snd (run_state (monfib (Suc (Suc 4))) x)) = fst(snd (run_state (monfib 4) x)) + fst(snd (run_state (monfib (Suc 4)) x))"


lemma monfib_aux: "fst(snd (run_state (monfib (Suc (Suc n))) x)) = fst(snd (run_state (monfib n) x)) + fst(snd (run_state (monfib (Suc n)) x))"
  apply (induction n arbitrary: x)
   apply (simp only:  skip_def fst_def snd_def)
   apply (simp add: get_def set_fst_def)
  sledgehammer


lemma fib_basic: "fst(snd(run_state (monfib n) x)) = fibacc n ((fst x)::nat) ((snd x)::nat)"
  apply (induction n arbitrary: x)
   apply (simp add:  skip_def)
  sorry


end