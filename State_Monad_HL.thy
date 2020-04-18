theory State_Monad_HL
imports 
  Main
  "~~/src/HOL/Library/State_Monad"
begin

definition TT:: "'a \<Rightarrow> bool" where "TT x = True"
definition TTT:: "'b \<Rightarrow> 'a \<Rightarrow> bool" where "TTT x y = True"
definition FF:: "'a \<Rightarrow> bool" where "FF x = False"
definition GG:: "('a \<Rightarrow> bool) \<Rightarrow> ('b => 'a \<Rightarrow> bool)" where "GG p x = p"
definition UU:: "('a \<Rightarrow> bool) \<Rightarrow> (unit => 'a \<Rightarrow> bool)" where "UU p x = p"

definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get_state:: "('a, 'a) state" where "get_state = State (\<lambda>x. (x,x))"
definition put_state:: "'a \<Rightarrow> ('a, unit) state" where "put_state x = State (\<lambda>_. ((),x))"
definition skip:: "('a, unit) state" where "skip = State (\<lambda>x. ((),x))"

definition get:: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) state" where 
  "get v = do { x \<leftarrow> get_state; return (v x) }"
definition put:: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> ('a, unit) state" where 
  "put vu a = do { x \<leftarrow> get_state; put_state (vu x a) }"

definition assign:: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, unit) state" where
  "assign vu v = do { a \<leftarrow> get v; put vu a }"

definition spec:: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) state \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where 
  "spec p S q = (\<forall>x. p x  \<longrightarrow> (let (y, z) = run_state S x in q y z))"

theorem get_state_rule: "spec (\<lambda>x. p x x) (get_state) p"
  by (simp add: get_state_def spec_def)

theorem get_rule: "\<forall>x. spec (\<lambda>y. p y \<and> v x = v y) (S (v x)) q \<Longrightarrow> spec p (get v \<bind> S) q"
  by (simp add: spec_def get_def return_def case_prod_unfold get_state_def)

theorem return_rule: "spec (p v) (return v) p"
  by (simp add: return_def spec_def)

theorem seq_rule: "\<lbrakk>spec p S q; \<forall>x. spec (q x) T r\<rbrakk> \<Longrightarrow> spec p (do { S; T }) r"
  apply (simp add: spec_def)
  by fastforce
  
theorem let_rule: "let v = E in spec p (do { T }) r \<Longrightarrow> spec p (do { let v = E; T }) r"
  by (simp add: spec_def snd_def)

theorem skip_left_rule: "spec p (do { skip; S }) q \<Longrightarrow> spec p S q"
  by (simp add: spec_def skip_def)

theorem conj_rule: "\<lbrakk>spec p S q; spec r S s\<rbrakk> \<Longrightarrow> spec (\<lambda>x. p x \<and> r x) S (\<lambda>x y. q x y \<and> s x y)"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

theorem conj_rule_right: "\<lbrakk>spec p S q; spec p S s\<rbrakk> \<Longrightarrow> spec p S (\<lambda>x y. q x y \<and> s x y)"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

theorem weaken_rule: "\<lbrakk>\<forall>x. (p x \<longrightarrow> p0 x); spec p0 S q\<rbrakk> \<Longrightarrow> spec p S q"
  by (simp add: spec_def)

theorem strengthen_rule: "\<lbrakk>\<forall>x y. (q0 x y \<longrightarrow> q x y); spec p S q0\<rbrakk> \<Longrightarrow> spec p S q"
  apply (simp add: spec_def)
  by (simp add: case_prod_unfold)

theorem cond_rule: "\<lbrakk>spec (\<lambda>x. p x \<and> b) S q; spec (\<lambda>x. p x \<and> \<not>b) T q\<rbrakk> \<Longrightarrow> spec p (if b then S else T) q"
  by (simp add: spec_def)

end