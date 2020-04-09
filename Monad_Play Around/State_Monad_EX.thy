theory State_Monad_EX
imports 
  Main
  "State_Monad_HL"
begin

record S1 =
  x_S1:: int
  y_S1:: int
  z_S1:: int

(* update functions *)

definition x_S1u:: "S1 \<Rightarrow> int \<Rightarrow> S1" where "x_S1u s v = s \<lparr> x_S1 := v \<rparr>"
definition y_S1u:: "S1 \<Rightarrow> int \<Rightarrow> S1" where "y_S1u s v = s \<lparr> y_S1 := v \<rparr>"
definition z_S1u:: "S1 \<Rightarrow> int \<Rightarrow> S1" where "z_S1u s v = s \<lparr> z_S1 := v \<rparr>"

theorem put_x_rule: "spec (\<lambda>x. p () (x \<lparr> x_S1 := v \<rparr>)) (put x_S1u v) p"
  by (simp add: spec_def put_def get_state_def put_state_def x_S1u_def)

theorem put_y_rule: "spec (\<lambda>x. p () (x \<lparr> y_S1 := v \<rparr>)) (put y_S1u v) p"
  by (simp add: spec_def put_def get_state_def put_state_def y_S1u_def)

theorem put_z_rule: "spec (\<lambda>x. p () (x \<lparr> z_S1 := v \<rparr>)) (put z_S1u v) p"
  by (simp add: spec_def put_def get_state_def put_state_def z_S1u_def)

(* simple programs *)

definition setx0:: "(S1, unit) state" where "setx0 = put x_S1u 0"
definition sety0:: "(S1, unit) state" where "sety0 = put y_S1u 0"
definition setz0:: "(S1, unit) state" where "setz0 = put z_S1u 0"

definition p0:: "S1 \<Rightarrow> bool" where "p0 s = (x_S1 s = 0 \<and> y_S1 s = 0 \<and> z_S1 s = 0)"

definition init0:: "(S1, unit) state" where
  "init0 = do { setx0; sety0; setz0 }"

lemma "spec TT init0 (GG p0)"
  apply(simp add: init0_def)
  apply(intro seq_rule[of _ _ "\<lambda>_ s. x_S1 s = 0"])
   apply(simp add: TT_def spec_def setx0_def put_def get_state_def put_state_def x_S1u_def)
  apply (intro allI)
  apply(intro seq_rule[of _ _ "\<lambda>_ s. x_S1 s = 0 \<and> y_S1 s = 0"])
   apply(simp add: spec_def sety0_def put_def get_state_def put_state_def y_S1u_def)
  by(simp add: spec_def setz0_def put_def get_state_def put_state_def GG_def p0_def z_S1u_def)

definition let0:: "(S1, unit) state" where "let0 = do { assign y_S1u x_S1; assign z_S1u x_S1 }"

definition q0:: "S1 \<Rightarrow> bool" where "q0 s = (x_S1 s = y_S1 s \<and> x_S1 s = z_S1 s)"

definition q1:: "unit \<Rightarrow> S1 \<Rightarrow> bool" where "q1 _ s = (x_S1 s = y_S1 s)"

lemma "spec TT let0 (GG q0)"
  apply (simp add: let0_def GG_def)
  apply (intro seq_rule[of _ _ "\<lambda>_ s. (x_S1 s = y_S1 s)"])
   apply (simp add: spec_def TT_def q1_def assign_def return_def get_def put_def get_state_def put_state_def y_S1u_def)
  by (simp add: spec_def GG_def q0_def assign_def get_def return_def put_def get_state_def put_state_def z_S1u_def)

end