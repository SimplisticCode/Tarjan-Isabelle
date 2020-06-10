theory NoDet_Monad_HL
  imports 
    Main
    "UTP_Monad"
begin       

definition TT:: "'a \<Rightarrow> bool" where "TT x = True"
definition TTT:: "'b \<Rightarrow> 'a \<Rightarrow> bool" where "TTT x y = True"
definition FF:: "'a \<Rightarrow> bool" where "FF x = False"
definition GG:: "('a \<Rightarrow> bool) \<Rightarrow> ('b => 'a \<Rightarrow> bool)" where "GG p x = p"
definition UU:: "('a \<Rightarrow> bool) \<Rightarrow> (unit => 'a \<Rightarrow> bool)" where "UU p x = p"

record status =
    ok:: bool 

definition var:: "(('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> bool" where
  "var x \<equiv> let (xa,xu) = x in (\<forall>v x. (xa o (xu v)) x = v) \<and> (\<forall>v. xu (xa v) v = v)"

definition ind:: "(('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> bool" where
  "ind x y \<equiv> let (xa,xu) = x in let (ya,yu) = y in 
    var x \<and> var y \<longrightarrow> (\<forall>v x. (xa o (yu v)) x = xa x) \<and> (\<forall>v x. (ya o (xu v)) x = ya x)"

fun indl:: "(('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) list \<Rightarrow> bool" where
  "indl x [] = True"
| "indl x (y#ys) = (ind x y \<and> indl x ys)"

fun dcl:: "(('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) list \<Rightarrow> bool" where
  "dcl [] = True"
| "dcl (x#xs) = (var x \<and> dcl xs \<and> indl x xs)"

text\<open>The axioms of variables described in the book Refinement calculus \<close>
text\<open>This axiom states that if we set variable x to v the value of x will be equal to b\<close>
theorem var_assign_ax1: "\<lbrakk>dcl [(xa, xu), (ya,yu)]\<rbrakk> \<Longrightarrow> (xa o (xu (ya v))) w = ya v"
  by (simp add: var_def)

text\<open>Attributes can be set independently of each other\<close>
theorem var_assign_ax2: "\<lbrakk>dcl [(xa, xu), (ya,yu)]\<rbrakk> \<Longrightarrow> v \<noteq> ya x \<longrightarrow> (xa o (xu v)) x \<noteq> ya x"
  by (smt case_prodE case_prod_conv dcl.simps(2) var_def)

text\<open>Two assignments to the same record following each other will ignore the first assignment\<close>
theorem var_assign_ax3: "\<lbrakk>dcl [(xa, xu)]\<rbrakk> \<Longrightarrow> (xa o (xu v) o (xu y)) x = v"
  using var_def
  by (simp add: var_def)

text\<open>An assignment with the current value of the variable doesn't change the state\<close>
theorem var_assign_ax4: "\<lbrakk>dcl [(xa, xu)]\<rbrakk> \<Longrightarrow> xa x = v \<longrightarrow> (xa o (xu v)) x = v"
  using var_def
  by (simp add: var_def)

text\<open>An assignment of a variable to itself doesn't change the state - it is equivalent to a skip\<close>
theorem var_assign_ax5: "\<lbrakk>dcl [(xa, xu)]\<rbrakk> \<Longrightarrow> (xa o (xu (xa x))) x = (xa x)"
  using var_assign_ax4 by fastforce  


definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = UTP_Monad.return"
definition get_state:: "('a, 'a) state" where "get_state = State (\<lambda>x. {(x,x)})"
definition put_state:: "'a \<Rightarrow> ('a, unit) state" where "put_state x = State (\<lambda>_. {((),x)})"
definition skip:: "('a, unit) state" where "skip = State (\<lambda>x. {((),x)})"

type_synonym ('a, 'b) vr = "('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)"
definition get:: "('a, 'b) vr \<Rightarrow> ('a, 'b) state" where 
  "get v = do { x \<leftarrow> get_state; return ((fst v) x) }"

definition put:: "('a, 'b) vr \<Rightarrow> 'b \<Rightarrow> ('a, unit) state" where 
  "put v a = do { x \<leftarrow> get_state; put_state ((snd v) a x)}"

definition assign:: "('a, 'b) vr \<Rightarrow> ('a, 'b) vr \<Rightarrow> ('a, unit) state" ("(2_ :=/ _)" [70, 65] 61) where
  "assign v w = do { a \<leftarrow> get w; put v a}"

text\<open>Make pre- and post-condition to a set of predicates\<close>
definition spec:: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) state \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<turnstile> _/ (2_)/ _)" [100, 55, 100] 50) where  
  "spec p S q = (\<forall>x y z. p x  \<longrightarrow> ((z, y) \<in> run_state S x \<longrightarrow> q y))"

theorem var_assign_skip: "\<lbrakk>dcl [x]\<rbrakk> \<Longrightarrow> \<turnstile> p (x := x) p"
  apply(simp add: spec_def var_def assign_def get_def put_def put_state_def get_state_def return_def; clarify)
  by(simp add: fst_def snd_def)

text\<open>Hoare's assignment axiom\<close>
theorem assign_rule: "\<lbrakk>dcl [x, y]; x=(xa,xu); y=(ya,yu)\<rbrakk> \<Longrightarrow> spec (\<lambda>v. p v \<and> xa v = ya v) (x := y) p"
  apply(simp add: spec_def var_def assign_def get_def put_def put_state_def get_state_def return_def; clarify)
  apply(simp add: fst_def snd_def ind_def var_def; clarify)  
  by metis

subsection\<open>Hoare logic\<close>
text\<open>Rules based on section 3 in Verification of Sequential and Concurrent Programs\<close>
theorem get_state_rule: "spec (\<lambda>x. p x) (get_state) p"
  by (simp add: get_state_def spec_def)


text\<open>The sequential rule describes all intermediate states that can be both a post-condition of statement @{text S} 
  with the pre-condition @{text p} which after execution of statement @{text T} will result in a final-state of @{text r}\<close>
theorem seq_rule: "\<lbrakk>spec p S q; spec q T r\<rbrakk> \<Longrightarrow> spec p (do { S; T }) r"
  apply (simp add: spec_def)
  by fastforce

text\<open>Rule to capture scope of local variables\<close>
theorem let_rule: "let v = E in spec p (do { T }) r \<Longrightarrow> spec p (do { let v = E; T }) r"
  by (simp add: spec_def snd_def)


text\<open>Pre- and post-conditions can be conjoined\<close>
theorem conj_rule: "\<lbrakk>spec p S q; spec r S s\<rbrakk> \<Longrightarrow> spec (\<lambda>x. p x \<and> r x) S (\<lambda>x. q x \<and> s x)"
  apply (simp add: spec_def)
  by blast

text\<open>A conjunction of the post-condition can be split up and be proved separately\<close>
theorem conj_rule_right: "\<lbrakk>spec p S q; spec p S s\<rbrakk> \<Longrightarrow> spec p S (\<lambda>x. q x \<and> s x)"
  by (simp add: spec_def)

text\<open>A pre-condition be weaken if it still preserves the post-condition (Weakest pre-condition)\<close>
theorem weaken_rule: "\<lbrakk>\<forall>x. (p x \<longrightarrow> p0 x); spec p0 S q\<rbrakk> \<Longrightarrow> spec p S q"
  apply (simp add: spec_def)
  by blast

text\<open>A post-condition can be strengthen if it gets preserved by the pre-condition\<close>
theorem strengthen_rule: "\<lbrakk>\<forall>x. (q0 x \<longrightarrow> q x); spec p S q0\<rbrakk> \<Longrightarrow> spec p S q"
  by (simp add: spec_def)

(*
lemma CondRule:
 "p (\<lambda>s. (b s \<longrightarrow> w s) \<and> (\<not>b s \<longrightarrow> w' s))
  \<Longrightarrow> spec w c1 q \<Longrightarrow> spec w' c2 q \<Longrightarrow> spec p (Cond b c1 c2) q"
by (auto simp:Valid_def)
*)
text\<open>A conditional statement can be split up into multiple proofs with difference assumptions (based on the queteria)\<close>
theorem cond_rule: "\<lbrakk>spec (\<lambda>x. p x \<and> b) S q; spec (\<lambda>x. p x \<and> \<not>b) T q\<rbrakk> \<Longrightarrow> spec p (COND b S T) q"
  by (simp add: spec_def)

(*
definition
  "whileLoop C B \<equiv> (\<lambda>r s.
     ({(r',s'). (Some (r, s), Some (r', s')) \<in> whileLoop_results C B},
        (Some (r, s), None) \<in> whileLoop_results C B \<or> (\<not> whileLoop_terminates C B r s)))"
*)
type_synonym 'a bexp = "('a, unit) state \<Rightarrow> bool"

datatype  ('a) com =
  Basic "('a, unit) state \<Rightarrow> ('a, unit)state"
| Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
| Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
| While "'a bexp" "'a bexp" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "('a, unit) state  => ('a, unit) state  => bool"

primrec iter :: "nat \<Rightarrow> 'a bexp \<Rightarrow> 'a sem \<Rightarrow> 'a sem"
  where
    "iter 0 b S s s' \<longleftrightarrow> \<not>b s \<and> s = s'"
  | "iter (Suc n) b S s s' \<longleftrightarrow> b s \<and> (\<exists>s''. S s s'' \<and> iter n b S s'' s')"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) s (f s)"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (c1;c2) s s'"
| "b s \<Longrightarrow> Sem c1 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "\<not>b s \<Longrightarrow> Sem c2 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "\<not>b s \<Longrightarrow> Sem (While b x c) s s"
| "b s \<Longrightarrow> Sem c s s'' \<Longrightarrow> Sem (While b x c) s'' s' \<Longrightarrow>
   Sem (While b x c) s s'"


primrec Sem1 :: "'a com \<Rightarrow> 'a sem"
  where
    "Sem1 (Basic f) s s' \<longleftrightarrow> s' = f s"
  | "Sem1 (c1; c2) s s' \<longleftrightarrow> (\<exists>s''. Sem c1 s s'' \<and> Sem c2 s'' s')"
  | "Sem1 (Cond b c1 c2) s s' \<longleftrightarrow> (if b s then Sem c1 s s' else Sem c2 s s')"
  | "Sem1 (While b x c) s s' \<longleftrightarrow> (\<exists>n. iter n b (Sem c) s s')"
    
inductive_cases [elim!]:
  "Sem (Basic f) s s'" 
  "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "Valid p c q \<longleftrightarrow> (\<forall>s s'. Sem c s s' \<longrightarrow> p s \<longrightarrow> q s')"

lemma SkipRule: "Valid p (Basic id) p"
by (auto simp:Valid_def)

(*
lemma BasicRule: "(\<lambda>s. p (f s)) = q \<Longrightarrow> Valid p (Basic f) q"
  apply (auto simp:Valid_def)
  sledgehammer
*)

lemma SeqRule: "\<lbrakk>Valid P c1 Q; Valid Q c2 R\<rbrakk> \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

theorem cond_rule1: "\<lbrakk>Valid (\<lambda>x. p x \<and> b x) S q; Valid (\<lambda>x. p x \<and> \<not>b x) T q\<rbrakk> \<Longrightarrow> Valid p (Cond b S T) q"
  by (auto simp:Valid_def)

lemma While_aux:
  assumes "Sem (WHILE b INV {i} DO c OD) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> I s \<and> b s \<longrightarrow> I s' \<Longrightarrow>
    I s \<Longrightarrow> I s'\<and> \<not>b s'"
  using assms
  by (induct "WHILE b INV {i} DO c OD" s s') auto

lemma while_rule: "Valid (\<lambda>s. P s \<and> b s) c P \<Longrightarrow> Valid (\<lambda>s. P s) (WHILE b INV {X} DO c OD) (\<lambda>s. P s \<and> \<not>b s)"
  by (smt Valid_def While_aux)

text\<open>Rule to capture scope of local variables\<close>
theorem let_rule1: "let v = E in Valid p (do { T }) r \<Longrightarrow> Valid p (do { let v = E; T }) r"
  by (simp add: spec_def snd_def)

text\<open>Pre- and post-conditions can be conjoined\<close>
theorem conj_rule1: "\<lbrakk>Valid p S q; Valid r S s\<rbrakk> \<Longrightarrow> Valid (\<lambda>x. p x \<and> r x) S (\<lambda>x. q x \<and> s x)"
  by (simp add: Valid_def)

text\<open>A conjunction of the post-condition can be split up and be proved separately\<close>
theorem conj_rule_right1: "\<lbrakk>Valid p S q; Valid p S s\<rbrakk> \<Longrightarrow> Valid p S (\<lambda>x. q x \<and> s x)"
  by (simp add: Valid_def)

text\<open>A pre-condition be weaken if it still preserves the post-condition (Weakest pre-condition)\<close>
theorem weaken_rule1: "\<lbrakk>\<forall>x. (p x \<longrightarrow> p0 x); Valid p0 S q\<rbrakk> \<Longrightarrow> Valid p S q"
  by (simp add: Valid_def)

text\<open>A post-condition can be strengthen if it gets preserved by the pre-condition\<close>
theorem strengthen_rule1: "\<lbrakk>\<forall>x. (q0 x \<longrightarrow> q x); Valid p S q0\<rbrakk> \<Longrightarrow> Valid p S q"
  by (simp add: Valid_def)






(*While loop and extensive records of state. Read chapters 0-4.*)


end