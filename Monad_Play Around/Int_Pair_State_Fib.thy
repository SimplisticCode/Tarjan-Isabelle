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
lemma[simp]: "fibacc (Suc(Suc n)) 0 1 = fib n + fib (Suc n)"
proof (induction n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  have "fibacc (Suc (Suc n)) (fib 1) (fib 2) = fibacc (Suc (Suc (Suc (Suc n)))) 0 1"
  proof(induction n rule: fibacc.induct)
    case (1 a b)
    then show ?case by simp
  next
    case (2 a b)
    then show ?case sorry
  next
    case (3 n a b)
    then show ?case sorry
  qed
  then show ?case 
qed
  
value \<open>fibacc 6 0 1 = 8\<close>
value \<open>fibacc 9 0 1 = 34\<close>

text\<open>Experiment with finding a pattern to extract in the proof\<close>
value \<open>fibacc 2 (fib 7) (fib 8)\<close>
value \<open>fibacc 8 (fib 1) (fib 2)\<close>
value \<open>fibacc 6 (fib 1) (fib 2)\<close>
value \<open>fib 5 + fibacc (Suc 5) 0 1 = fib 7\<close>
value \<open>fib (Suc 5) + fibacc 5 0 1 = fib 7\<close>

value \<open>fibacc 5 (fib 1) (fib 2)\<close>

text\<open>Stefan I need some help here\<close>
lemma fibacc1: "fibacc n a b + fibacc (Suc n) a b = fibacc (Suc (Suc n)) a b"
proof(induct n arbitrary: a b rule: fibacc.induct)
  case (1 a b)
  fix a and b
  have 1:"fibacc 0 a b = a" by simp
  from this have 2:"fibacc (Suc 0) a b = b" by simp
  from 1 and 2 have 3:"fibacc (Suc (Suc 0)) a b = a + b" by simp
  then show ?case by simp
next
  case (2 a b)
  then show ?case sorry
next
  case (3 n a b)
  then show ?case sorry
qed


lemma fib_wrap1: "fibacc n 0 1 = fib n"
proof (induct n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  then show ?case sledgehammer
qed sorry

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

lemma fibacc_gre[simp]: "fibacc n a b \<le> fibacc (Suc n) a b"
proof(induct n arbitrary: a b rule: fibacc.induct)
  case (1 a b)
  fix n 
  then show ?case sledgehammer
next
  case (2 a b)
  then show ?case s
next
  case (3 n a b)
  then show ?case sorry
qed

lemma: "fibacc (Suc(Suc 0)) (fib n) (fib (Suc n)) = fibacc (Suc (Suc (Suc(Suc n)))) 0 1"
proof(induct n rule: fibacc.induct)
case (1 a b)
then show ?case by simp
next
  case (2 a b)
  then show ?case sorry
next
  case (3 n a b)
then show ?case sorry
qed





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
  proof (induction n rule: fibacc.induct)
    case (1 a b)
    assume "a = 0" 
    also assume "b = 1"
    then show ?case by simp
  next
    case (2 a b)
    assume "a = 0 \<and> b = 1" 
    then show ?case sorry
  next
    case (3 n a b)
    then show ?case sorry
  qed
    case 0
    then show ?case by simp
  next
    case (Suc n)
    fix n
    assume "fibacc (Suc n) 0 1 > 0"
    from this have "fibacc (Suc(Suc n)) 0 1 \<ge> fibacc (Suc n) 0 1"
      using fibacc_gre by blast 
      show "0 < fibacc (Suc(Suc n)) 0 1"
        using \<open>0 < fibacc (Suc n) 0 1\<close> and \<open> fibacc (Suc (Suc n)) 0 1  \<ge> fibacc (Suc n) 0 1\<close>  by simp
    qed
  

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