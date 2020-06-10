theory BinarySearch
imports 
  "variable"
begin

subsection\<open>Definition of the environment\<close>
record env = 
  right :: "nat"
  left  :: "nat"
  arr   :: "nat list"
  mid   :: "nat"
  val   :: "nat"

subsubsection\<open>Monad update functions\<close>
text\<open>Each of the definitions takes an environment and a value of one of the variables. They update the value of the variable and outputs a new environment.\<close>
definition right_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "right_Env s v = s \<lparr> right := v \<rparr>"
definition left_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "left_Env s v = s \<lparr> left := v \<rparr>"
definition arr_Env:: "env \<Rightarrow> nat list  \<Rightarrow> env" where "arr_Env s v = s \<lparr> arr := v \<rparr>"
definition mid_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "mid_Env s v = s \<lparr> mid := v \<rparr>"
definition val_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "val_Env s v = s \<lparr> val := v \<rparr>"

text\<open>I think the update functions should be changed to have the same signature as in the Refinement Calculus book\<close>
definition right_Env1:: "nat \<Rightarrow> env \<Rightarrow> env" where "right_Env1 v s = s \<lparr> right := v \<rparr>"
definition left_Env1:: "nat \<Rightarrow> env \<Rightarrow> env" where "left_Env1 v s = s \<lparr> left := v \<rparr>"
definition arr_Env1:: "nat list \<Rightarrow> env \<Rightarrow> env" where "arr_Env1 v s = s \<lparr> arr := v \<rparr>"
definition mid_Env1:: "nat \<Rightarrow> env \<Rightarrow> env" where "mid_Env1 v s = s \<lparr> mid := v \<rparr>"
definition val_Env1:: "nat \<Rightarrow> env \<Rightarrow> env" where "val_Env1 v s = s \<lparr> val := v \<rparr>"

text\<open>Should I make a get function?\<close>
definition right_get:: "env \<Rightarrow> nat" where "right_get s = right s"
definition left_get:: "env \<Rightarrow> nat" where "left_get s = left s"
definition arr_get:: "env \<Rightarrow>nat list" where "arr_get s = arr s"
definition mid_get:: "env \<Rightarrow>nat" where "mid_get s = mid s"
definition val_get:: "env \<Rightarrow>nat" where "val_get s = val s"

text\<open>Variable definitions\<close>

subsubsection\<open>Theorems about how the update functions changes the environment\<close>

theorem put_right_rule: "\<lbrakk>dcl [x]; x=(xa,xu)\<rbrakk> \<Longrightarrow> spec {v. v \<in> p \<and> right_get v = xa v} ((right_get, right_Env1) := x) p"
  apply (simp add: spec_def put_def get_state_def assign_def put_state_def var_def; clarify)
  apply(simp add: right_get_def right_Env1_def)
  by (metis env.surjective env.update_convs(1))

theorem put_left_rule: "spec (\<lambda>x. p () (x \<lparr> left := v \<rparr>)) (put left_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def left_Env_def)

theorem put_arr_rule: "spec (\<lambda>x. p () (x \<lparr> arr := v \<rparr>)) (put arr_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def arr_Env_def)

theorem put_mid_rule: "spec (\<lambda>x. p () (x \<lparr> mid := v \<rparr>)) (put mid_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def mid_Env_def)

theorem put_val_rule: "spec (\<lambda>x. p () (x \<lparr> val := v \<rparr>)) (put val_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def val_Env_def)


subsection\<open>Definitions of the methods\<close>
definition update_left where
  "update_left \<equiv> do{
    (left_get,left_Env1) := (mid_get, mid_Env1)
  }"

definition update_right where
  "update_right \<equiv> do{
    (right_get,right_Env1) := (mid_get, mid_Env1)
  }"

end