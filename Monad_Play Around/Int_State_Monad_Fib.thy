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
"fib_wrap n = fibacc n 0 1"

fun fib :: "nat => nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"

fun monfibacc :: "nat \<Rightarrow> nat => (nat, unit) state" where
m1:  "monfibacc 0 a =  do{put a}"| 
m2:  "monfibacc (Suc 0) a = do{b \<leftarrow> get; put b}"| 
m3:  "monfibacc (Suc n) a  = do{b \<leftarrow> get; new_b \<leftarrow> return (a + b); put new_b; monfibacc n b}"


value \<open>fibacc 10 0 1 = 55\<close>
value \<open>fib 5\<close>
value "snd (run_state (monfibacc 5 0) (1::nat))"
value \<open>snd (run_state (monfibacc 10 0) (1::nat)) = 55\<close>
value \<open>fib 10 = 55\<close>
value \<open>snd (run_state (monfib_wrap 9) (1::nat))\<close>
value \<open>snd (run_state (monfib_wrap 2) (0::nat))\<close>
value \<open>snd (run_state (monfib_wrap 0) (snd (run_state (monfib_wrap 7) 1)))\<close>
value \<open>snd (run_state (monfib_wrap 7) 1)\<close>

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
    using fib_aux by simp
qed

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
  apply(induction n rule: nat.induct)
    apply(simp_all add: fib_main1 fibwrap_main)
  done

lemma monfib_aux: "snd (run_state(monfibacc n b) (a + b)) = snd (run_state(monfibacc (Suc n) a) (b))"
  apply (induction n arbitrary: a b rule:nat.induct)
   apply (simp_all add: snd_def put_def get_def return_def)
  done

value\<open>snd (run_state(monfibacc 7 0) 1) + snd (run_state(monfibacc (Suc 7) 0) 1) =snd (run_state(monfibacc (Suc (Suc 7)) 0) 1)\<close>

lemma monfib_aux1: "snd (run_state(monfibacc (Suc (Suc n)) a) b) = snd (run_state(monfibacc n a) b) + snd (run_state(monfibacc (Suc n) a) b)"
proof(induct n arbitrary: a b)
  case 0
  then show ?case by(simp add: snd_def put_def get_def return_def)
next
  case (Suc nat)
  then show ?case
    using monfib_aux by (simp add: snd_def put_def get_def return_def)
qed

lemma fib_m_main: "snd (run_state (monfibacc n 0) 1) = fib n"
  apply (induction n rule:fib.induct)
    apply(simp add: snd_def put_def get_def return_def)
    apply(simp add: snd_def put_def get_def return_def)
    apply(simp only: monfib_aux1)
  apply(simp)
  done


lemma fib_mon_main: "snd (run_state (monfibacc n a) (b+a)) = fibacc n a (b+a)"
  apply (induction n rule:nat.induct)
    apply(simp add: snd_def put_def get_def return_def)
    apply(simp add: snd_def put_def get_def return_def)


lemma fib_mon_main: "snd (run_state (monfibacc n a) b) = fibacc n a b"
  apply (induction n rule:nat.induct)
   apply(simp add: snd_def put_def get_def return_def)
  try0


end