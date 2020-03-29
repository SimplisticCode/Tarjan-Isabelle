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

definition fib_wrap:: "nat \<Rightarrow> nat" where
"fib_wrap n = fibacc n 0 1"

fun fib :: "nat => nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"


value "fib (Suc (Suc 6)) "

  
value \<open>fibacc 6 0 1 = 8\<close>
value \<open>fibacc 9 0 1 = 34\<close>

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
proof(induct n arbitrary: a b)
  case 0
  then show ?case by simp_all
next
  case (Suc nat)
  then show ?case
    using fib_aux by simp_all
qed

lemma fib_main1: "fib n = fibacc n 0 1"
  apply(induction n rule: fib.induct)
    apply(simp)
    apply(simp)
    apply (simp only: fib_aux1)
  by (simp)


lemma fib_aux3[simp]: "fibacc (Suc n) 0 1 = fibacc n (fibacc (Suc 0) 0 1) (fibacc (Suc (Suc 0)) 0 1)"
proof(induct n rule: nat.induct)
  case zero
  then show ?case by simp
next
  case (Suc nat)
  then show ?case by simp
qed

lemma fib_aux4[simp]: "fibacc  n (fib (Suc 0)) (fib (Suc (Suc 0))) = fibacc n (fibacc (Suc 0) 0 1) (fibacc (Suc (Suc 0)) 0 1)"
proof(induct n rule: nat.induct)
  case zero
  then show ?case by simp
next
  case (Suc nat)
  then show ?case by simp
qed

lemma fib_gre[simp]: "fib n \<le> fib (Suc n)"
proof(induction n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  then show ?case by simp
qed

lemma fibacc_gre[simp]: "\<forall> (a::nat) (b::nat). a \<le> b \<Longrightarrow> fibacc n a b \<le> fibacc (Suc n) a b"
  apply(induction n)
   apply (simp_all)

primrec pow :: "nat => nat => nat" where 
    "pow x 0 = Suc 0"
  | "pow x (Suc n) = x * pow x n"

definition 
 "ipow x n = (if n < 0 then (1 / x) ^ nat (-n) else x ^ nat n)"
(*
lemma d : "\<forall>x \<ge> 1. ((int(fib (Suc(Suc x))) * int(fib x)) - (int(fib (Suc x) ^ 2))) = (if x mod 2 \<noteq> 0 then -1 else 1)"
proof (induction x)
*)

lemma [simp]: "fibacc (Suc n) 0 1 > 0"
  apply (induction n rule: nat.induct)
   apply(simp_all)
  sledgehammer

  

lemma [simp]: "fib (Suc n) > 0"
proof(induction n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  then show ?case by simp
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

value \<open>fst(snd(run_state (monfib 5) (0::nat,x::nat)))\<close>
value "fst(snd (run_state (monfib 6) x))"

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
proof (induction n)
  case 0
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed


lemma fib_aux: "fibacc n (fst x) (snd x) + fibacc (Suc n) (fst x) (snd x) = fibacc (Suc(Suc n)) (fst x) (snd x)"
  apply(induction n arbitrary: x)
   apply simp
  sledgehammer



lemma fib_basic: "fst(snd(run_state (monfib n) x)) = fibacc n ((fst x)::nat) ((snd x)::nat)"
  apply (induction n arbitrary: x)
   apply (simp add:  skip_def)
  sorry


end