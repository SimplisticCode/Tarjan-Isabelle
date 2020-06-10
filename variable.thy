theory variable
imports 
  Main
  "~~/src/HOL/Library/State_Monad"
begin

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

definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get_state:: "('a, 'a) state" where "get_state = State (\<lambda>x. (x,x))"
definition put_state:: "'a \<Rightarrow> ('a, unit) state" where "put_state x = State (\<lambda>_. ((),x))"
definition skip:: "('a, unit) state" where "skip = State (\<lambda>x. ((),x))"

definition get:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) state" where 
  "get v = do { x \<leftarrow> get_state; return (v x) }"

definition put:: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>  'b \<Rightarrow> ('a set, unit) state" where 
  "put vu a = do { x \<leftarrow> get_state; put_state { z. (\<exists>y \<in> x. z = vu a y) } }"

definition assign:: "(('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a \<Rightarrow> 'a)) \<Rightarrow> ('a set, unit) state" ("(2_ :=/ _)" [70, 65] 61) where
  "assign x y \<equiv> do { v \<leftarrow> get_state; put_state { z. (\<exists>u \<in> v. z = (snd x) (fst y u) u) }}"

text\<open>Make pre- and post-condition to a set of predicates\<close>
definition spec:: "'a set \<Rightarrow> ('a set, unit) state \<Rightarrow> 'a set \<Rightarrow> bool" ("(3\<turnstile> _/ (2_)/ _)" [100, 55, 100] 50) where 
  "spec p S q = (\<forall>x. x \<in> p \<longrightarrow> (let (_, z) = run_state S {x} in z \<subseteq> q))"

theorem var_assign_skip: "\<lbrakk>dcl [x]\<rbrakk> \<Longrightarrow> \<turnstile> {s. s \<in> p} (x := x) {s. s \<in> p}"
  apply(simp add: spec_def var_def assign_def get_def put_def put_state_def get_state_def return_def; clarify)
  by(simp add: fst_def snd_def)

text\<open>Hoare's assignment axiom\<close>
theorem assign_rule: "\<lbrakk>dcl [x, y]; x=(xa,xu); y=(ya,yu)\<rbrakk> \<Longrightarrow> spec {v. v \<in> p \<and> xa v = ya v} (x := y) (p)"
  apply(simp add: spec_def var_def assign_def get_def put_def put_state_def get_state_def return_def; clarify)
  apply(simp add: fst_def snd_def ind_def var_def; clarify)  
  by metis

theorem seq_rule: "\<lbrakk>spec p S q; spec q T r\<rbrakk> \<Longrightarrow> spec p (do { S; T }) r"
  apply (simp add: spec_def run_state_def; clarify)
  sorry
  
theorem let_rule: "let v = E in spec p (do { T }) r \<Longrightarrow> spec p (do { let v = E; T }) r"
  by (simp add: spec_def snd_def)

theorem skip_left_rule: "spec p (do { skip; S }) q \<Longrightarrow> spec p S q"
  by (simp add: spec_def skip_def)

theorem conj_rule: "\<lbrakk>spec p S q; spec r S s\<rbrakk> \<Longrightarrow> spec (p \<inter> r) S (s \<inter> q)"
  apply (simp add: spec_def)
  by fastforce

theorem conj_rule_right: "\<lbrakk>spec p S q; spec p S s\<rbrakk> \<Longrightarrow> spec p S (q \<inter> s)"
  apply (simp add: spec_def)
  by fastforce

text\<open>We can weaken the postcondition, i.e. conclude less than we are allowed to\<close>
theorem weaken_rule: "\<lbrakk>\<forall>x. (x \<in> p \<longrightarrow> x \<in> p0); spec p0 S q\<rbrakk> \<Longrightarrow> spec p S q"
  by (simp add: spec_def)

text\<open>We can strengthen the precondition, i.e. assume more than we need\<close>
theorem strengthen_rule: "\<lbrakk>\<forall>x. (x \<in> q0 \<longrightarrow> x \<in> q); spec p S q0\<rbrakk> \<Longrightarrow> spec p S q"
  apply (simp add: spec_def)
  by fastforce

theorem cond_rule: "\<lbrakk>b \<and> spec p S q; \<not>b \<and> spec p T q\<rbrakk> \<Longrightarrow> spec p (if b then S else T) q"
  by (simp add: spec_def)

theorem cond_rule1: "\<lbrakk>spec {x. x \<in> p \<and> b} S q; spec {x. x \<in> p \<and> \<not>b} T q\<rbrakk> \<Longrightarrow> spec p (if b then S else T) q"
  by (simp add: spec_def)


text\<open>Assertion P in the while loop is called a loop invariant of the while loop since it holds both before and after execution.\<close>
theorem while_loop: "\<lbrakk>spec  (p \<inter> b) S p\<rbrakk> \<Longrightarrow> spec p (while b S) (p \<inter> -b)"
  apply (simp add: spec_def; clarify)
  sorry

theorem while_loop1: "\<lbrakk>spec {x. x \<in> p \<and> b} S p\<rbrakk> \<Longrightarrow> spec p (while b S) {x. x\<in> p \<and> \<not>b}"
  apply (simp add: spec_def run_state_def; clarify)
  sorry

text\<open>Add record to hold track of termination\<close>
record status =
  ok :: bool



end