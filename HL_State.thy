theory HL_State
imports 
  Main
  "~~/src/HOL/Library/State_Monad"
begin

section\<open>Introduction\<close>

section\<open>Hoare calculus\<close>
text\<open>Basic definitions that can be useful inside as a parameter to spec in a proof\<close>
definition TT:: "'a \<Rightarrow> bool" where "TT x = True"
definition TTT:: "'b \<Rightarrow> 'a \<Rightarrow> bool" where "TTT x y = True"
definition FF:: "'a \<Rightarrow> bool" where "FF x = False"
definition GG:: "('a \<Rightarrow> bool) \<Rightarrow> ('b => 'a \<Rightarrow> bool)" where "GG p x = p"
definition UU:: "('a \<Rightarrow> bool) \<Rightarrow> (unit => 'a \<Rightarrow> bool)" where "UU p x = p"

text\<open>Methods to get describe the basic state changes. These are described by state-monad which encapsulates the state\<close>
definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get_state:: "('a, 'a) state" where "get_state = State (\<lambda>x. (x,x))"
definition put_state:: "'a \<Rightarrow> ('a, unit) state" where "put_state x = State (\<lambda>_. ((),x))"

definition unpack_state:: "('a, unit) state \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "unpack_state S x \<equiv> snd(run_state S x)"


type_synonym 'a bexp = "'a \<Rightarrow> bool"
type_synonym 'a assn = "'a \<Rightarrow> bool"

subsubsection\<open>Commands\<close>
text\<open>Commands describe that can be done in the langagauge.\<close>
text\<open>I have assumed that all calls eventually be reduces to basic commands which involves manipulation of the state-monad.\<close>
datatype 'a com =
  Basic "('a, unit) state"
| Seq  "'a com" "'a com"                     ("(_;/ _)"      [61,60] 60)
| Cond "'a bexp" "'a com" "'a com"           ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)

text\<open>The skip-command is just a special command which leaves the state-monad unchanged. Put monad-identify - this should be a return\<close>
abbreviation annskip ("SKIP") where "SKIP == (State_Monad.return)"

type_synonym 'a sem = "('a, unit) state  => ('a, unit) state => bool"

text\<open>This could potentially be useful in the while-loop. 
  It states that the predicate is not longer true in the base case, but that the final state has also been reached.
  The other case states that be predicate is true and it is possible to reach the base-case in a finite amount of steps.
 It is taken from: \url{http://isabelle.in.tum.de/dist/library/HOL/HOL-Isar_Examples/Hoare.html}\<close>
(*primrec iter :: "nat \<Rightarrow> 'a bexp \<Rightarrow> 'a sem \<Rightarrow> 'a sem"
  where
    "iter 0 b S s s' \<longleftrightarrow> \<not>b s \<and> s = s'"
  | "iter (Suc n) b S s s' \<longleftrightarrow> b s \<and> (\<exists>s''. S s s'' \<and> iter n b S s'' s')"
*)

text\<open>The semantics describe how the program should be interpreted. It takes a command and returns two states - the pre and post state of each command.\<close>
inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) s (f)"
| "Sem c1 s s'' \<Longrightarrow> Sem c2  s'' s' \<Longrightarrow> Sem (c1;c2) s s'"
| "b s \<Longrightarrow> Sem c1 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "\<not>b s \<Longrightarrow> Sem c2 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" 
  "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "Valid p c q \<longleftrightarrow> (\<forall>s s'. Sem c s s' \<longrightarrow>  p s \<longrightarrow> q (unpack_state s' s))"

lemma SkipRule: "p = q \<Longrightarrow> Valid p SKIP q"
by (auto simp:Valid_def)

lemma BasicRule: "\<forall>s. p s \<longrightarrow> q (unpack_state (f s) s) \<Longrightarrow> Valid p (Basic f) q"
  by (auto simp:Valid_def)

lemma SeqRule: "Valid p c1 q  \<Longrightarrow> Valid q c2 r  \<Longrightarrow> Valid p (c1;c2) r"
  apply (auto simp:Valid_def)
  sorry


lemma CondRule:
 "\<forall>s. p s \<longrightarrow> ((b s \<longrightarrow> w s) \<and> (\<not>b s \<longrightarrow>  w' s))
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
  by (auto simp:Valid_def)

definition get:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) state" where 
  "get v = do { x \<leftarrow> get_state; return (v x) }"

definition put:: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> ('a, unit) state" where 
  "put vu a = do { x \<leftarrow> get_state; put_state (vu x a) }"

definition assign:: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, unit) state" where
  "assign vu v =  (do { a \<leftarrow> get v; put vu a })"

definition assign1 :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a com" ("(2_ :=/ _)" [70, 65] 61) where 
  "assign1 vu v = Basic (\<lambda>e. do { a \<leftarrow> get v; put vu a })" 

text\<open>This is what enables the \<close>
syntax
  "_hoare_vars" :: "[idts, 'a assn,'a com,'a assn] \<Rightarrow> bool" ("(VARS _ //{_} // _ // {_})" [0,0,55,0] 50)

text\<open>This is what enables the \<close>
syntax
  "_hoare" :: "['a assn,'a com,'a assn] => bool" ("({_} // _ // {_})" [0,55,0] 50)


definition spec:: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) state \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where 
  "spec p S q = (\<forall>x. p x  \<longrightarrow> (let (y, z) = run_state S x in q y z))"

subsection\<open>Hoare logic\<close>
text\<open>Rules based on section 3 in Verification of Sequential and Concurrent Programs\<close>
theorem get_state_rule: "spec (\<lambda>x. p x x) (get_state) p"
  by (simp add: get_state_def spec_def)


text\<open>Rule to extract a value from the Monad\<close>
theorem get_rule: "\<forall>x. spec (\<lambda>y. p y \<and> v x = v y) (S (v x)) q \<Longrightarrow> spec p (get v \<bind> S) q"
  by (simp add: spec_def get_def return_def case_prod_unfold get_state_def)

theorem return_rule: "spec (p v) (return v) p"
  by (simp add: return_def spec_def)

text\<open>The sequential rule describes all intermediate states that can be both a post-condition of statement @{text S} 
  with the pre-condition @{text p} which after execution of statement @{text T} will result in a final-state of @{text r}\<close>
theorem seq_rule: "\<lbrakk>spec p S q; \<forall>x. spec (q x) T r\<rbrakk> \<Longrightarrow> spec p (do { S; T }) r"
  apply (simp add: spec_def)
  by fastforce

text\<open>Rule to capture scope of local variables\<close>
theorem let_rule: "let v = E in spec p (do { T }) r \<Longrightarrow> spec p (do { let v = E; T }) r"
  by (simp add: spec_def snd_def)


text\<open>Pre- and post-conditions can be conjoined\<close>
theorem conj_rule: "\<lbrakk>spec p S q; spec r S s\<rbrakk> \<Longrightarrow> spec (\<lambda>x. p x \<and> r x) S (\<lambda>x y. q x y \<and> s x y)"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

text\<open>A conjunction of the post-condition can be split up and be proved separately\<close>
theorem conj_rule_right: "\<lbrakk>spec p S q; spec p S s\<rbrakk> \<Longrightarrow> spec p S (\<lambda>x y. q x y \<and> s x y)"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

text\<open>A pre-condition be weaken if it still preserves the post-condition (Weakest pre-condition)\<close>
theorem weaken_rule: "\<lbrakk>\<forall>x. (p x \<longrightarrow> p0 x); spec p0 S q\<rbrakk> \<Longrightarrow> spec p S q"
  by (simp add: spec_def)

text\<open>A post-condition can be strengthen if it gets preserved by the pre-condition\<close>
theorem strengthen_rule: "\<lbrakk>\<forall>x y. (q0 x y \<longrightarrow> q x y); spec p S q0\<rbrakk> \<Longrightarrow> spec p S q"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

text\<open>A conditional statement can be split up into multiple proofs with difference assumptions (based on the queteria)\<close>
theorem cond_rule: "\<lbrakk>spec (\<lambda>x. p x \<and> b) S q; spec (\<lambda>x. p x \<and> \<not>b) T q\<rbrakk> \<Longrightarrow> spec p (if b then S else T) q"
  by (simp add: spec_def)


end