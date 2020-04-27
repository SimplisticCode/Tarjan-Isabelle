theory Dutch_National_Flag_Monad_Eisbach
imports 
  "Dutch_National_Flag_Monad_Definitions"
  "HOL-Eisbach.Eisbach"
begin

method rewrite_env uses simps =
(match conclusion in "?P (x :: env)" for x \<Rightarrow>
  \<open>simp add: spec_def put_def get_state_def put_state_def return_def get_def simps\<close>)

method rewrite_env_all =
(match conclusion in "?P (x :: env)" for x \<Rightarrow>
  \<open>simp add: spec_def put_def get_state_def put_state_def return_def get_def high_Env_def i_Env_def low_Env_def xs_Env_def swap_def\<close>)

method all_Get_Seq =
(intro allI; simp; intro get_rule; intro allI)

method solve methods m = (m ; fail)

method prop_solver =
(rewrite_env_all; solve\<open>prop_solver\<close> | all_Get_Seq;  solve\<open>prop_solver\<close> )


end