theory BinarySearch1
imports 
  Main
  "../State_Monad_HL"
begin

text\<open>Definition of the environment\<close>
record env = 
  right :: "nat"
  left  :: "nat"
  arr   :: "nat list"
  mid   :: "nat"

subsection\<open>Monad update functions\<close>
text\<open>Each of the definitions takes an environment and a value of one of the variables. They update the value of the variable and outputs a new environment.\<close>
definition right_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "right_Env s v = s \<lparr> right := v \<rparr>"
definition left_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "left_Env s v = s \<lparr> left := v \<rparr>"
definition arr_Env:: "env \<Rightarrow> nat list  \<Rightarrow> env" where "arr_Env s v = s \<lparr> arr := v \<rparr>"
definition mid_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "mid_Env s v = s \<lparr> mid := v \<rparr>"


subsection\<open>Theorems about how the update functions changes the environment\<close>
theorem put_right_rule: "spec (\<lambda>x. p () (x \<lparr> right := v \<rparr>)) (put right_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def right_Env_def)

theorem put_left_rule: "spec (\<lambda>x. p () (x \<lparr> left := v \<rparr>)) (put left_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def left_Env_def)

theorem put_arr_rule: "spec (\<lambda>x. p () (x \<lparr> arr := v \<rparr>)) (put arr_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def arr_Env_def)

theorem put_mid_rule: "spec (\<lambda>x. p () (x \<lparr> mid := v \<rparr>)) (put mid_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def mid_Env_def)

subsection\<open>Definitions of the methods\<close>
definition update_left where
  "update_left \<equiv> do{
    mid \<leftarrow> get mid;
    put left_Env mid
  }"

definition update_right where
  "update_right \<equiv> do{
    mid \<leftarrow> get mid;
    put right_Env mid
  }"


definition update_range where
"update_range v \<equiv> do{
                    (mid, xs) \<leftarrow> get (\<lambda>e. (mid e, arr e));
                    (if xs ! mid \<le> v then do {
                        update_left  
                    }else
                        update_right
                    )
                }"

fun BinarySearch:: "nat \<Rightarrow> nat \<Rightarrow> (env, unit) state" where
  case0:"BinarySearch 0 _  = skip"|
  caseN:"BinarySearch (Suc n) v = do {
                        (l, r) \<leftarrow> get (\<lambda>e. (left e, right e));
                        put mid_Env ((r + l) div 2);
                        (if r \<noteq> Suc  l then do{
                          update_range v;
                          BinarySearch n v
                         }
                       else skip
                      )}"

text\<open>The definiton of how to set up the state-monad/environment with the right values based on an array.\<close>
definition init_env:: "nat list \<Rightarrow> env" where
  "init_env l \<equiv> \<lparr>right = length l,  left = 0, arr = sort(l), mid = 0\<rparr>"

value \<open>snd(run_state (BinarySearch 6 5) (init_env [0,3,2,1,5,8]))\<close>

subsection\<open>Definition of pre- and postcondition\<close>       
text\<open>The array shall be sorted and left is not greater than right\<close>
definition env_invariant:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"env_invariant v e \<equiv> sorted(arr e)
      \<and> left e \<le> right e \<and> right e \<le> length(arr e)"

definition p:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"p v e \<equiv> sorted(arr e) \<and> length(arr e) \<ge> 1
      \<and> left e \<le> right e \<and> right e \<le> length(arr e) \<and> arr e ! left e \<le> v \<and> arr e ! right e > v"

definition post_q where
"post_q v e \<equiv> (mid e < length (arr e) \<and> arr e ! mid e \<le> v \<and> v < arr e ! Suc (mid e))"

definition update_range_pre where
"update_range_pre v e \<equiv> p v e \<and> left e < right e \<and> mid e = ((left e + right e) div 2)"

definition update_left_pre where
"update_left_pre v e \<equiv> update_range_pre v e \<and> arr e ! mid e \<le> v"

definition update_right_pre where
"update_right_pre v e \<equiv> update_range_pre v e \<and> arr e ! (mid e) > v"

definition update_left_post where
"update_left_post v e \<equiv> left e = mid e"

definition update_right_post where
"update_right_post v e  \<equiv> right e = mid e"




lemma update_left_spec: "spec (update_left_pre v) update_left (GG (update_left_post v))"
  unfolding update_left_pre_def GG_def update_left_post_def 
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def put_def put_state_def get_state_def left_Env_def)


lemma update_right_spec: "spec (update_right_pre v) update_right (GG (update_left_post v))"
  unfolding update_right_pre_def GG_def update_right_post_def 
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  by (simp add: spec_def put_def put_state_def get_state_def left_Env_def)


definition update_range_pre_aux where
"update_range_pre_aux v e e2 \<equiv> e = e2 \<and> update_range_pre v e"

definition update_range_post where
"update_range_post v e e2 \<equiv> right e - left e > right e2 - left e2
                            \<and> p v e2
                            \<and> left e2 \<ge> left e 
                            \<and> right e2 \<le> right e2"

definition update_range_val_post where
"update_range_val_post v e e2 \<equiv> update_range_post v e e2
                              \<and> (Suc((right e + left e) div 2) = left e2 \<or> ((right e + left e) div 2) = right e2)"

definition update_val_post where
"update_val_post v e e2 \<equiv> right e - left e > right e2 - left e2
                            \<and> env_invariant v e2
                            \<and> (((right e + left e) div 2) = left e2 \<and> left e2 = right e2)"


definition update_val_pre where
"update_val_pre v e s \<equiv> e = s \<and> update_range_pre v e \<and> \<not>arr e ! ((right e + left e) div 2) > v \<and> \<not>arr e ! ((right e + left e) div 2) < v"

lemma isSmaller: "(x::nat) < y \<Longrightarrow> (y + x) div 2 < y"
  by linarith

lemma isGreater: "(x::nat) < y \<Longrightarrow> Suc((y + x) div 2) > x"
  by linarith

lemma isGreater1: "(x::nat) < y \<Longrightarrow> ((y + x) div 2) \<ge> x"
  by linarith



lemma update_left_spec: "spec (update_left_pre v e) update_left (GG (update_range_val_post v e))"
  unfolding update_left_pre_def GG_def update_range_pre_def update_range_post_def update_range_val_post_def env_invariant_def
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  using diff_less_mono2 apply auto[1]
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: isGreater le_less)
  by (simp add: spec_def put_def put_state_def get_state_def left_Env_def)

lemma update_right_spec: "spec (update_right_pre v e) update_right (GG (update_range_val_post v e))"
  unfolding update_right_pre_def GG_def update_range_pre_def update_range_post_def update_range_val_post_def env_invariant_def
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply auto[1]
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  using isGreater less_Suc_eq_le apply blast
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  by (simp add: spec_def put_def put_state_def get_state_def right_Env_def)

lemma update_val_spec: "spec (update_val_pre v e) update_val (GG (update_val_post v e))"
  unfolding update_val_pre_def GG_def update_range_pre_def update_val_post_def env_invariant_def
  apply(simp add: update_val_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  by linarith

lemma update_range_spec: "spec (update_range_pre_aux v e) (update_range v) (GG (update_range_post v e))"
  unfolding update_range_pre_aux_def GG_def update_range_post_def update_range_pre_def env_invariant_def
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp only: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  using diff_less_mono2 apply auto[1]
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: Suc_leI isSmaller)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  using isGreater less_or_eq_imp_le apply blast
  apply(simp only: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  using isGreater less_Suc_eq_le apply blast
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: update_val_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  using isGreater less_Suc_eq_le by blast


(*
lemma aux: "env_invariant v e \<and> right e = left e \<Longrightarrow> post_cond v e"
  unfolding post_cond_def env_invariant_def
  sledgehammer
  sorry
*)


lemma main1: "spec (env_invariant v) (BinarySearch n v) (GG (env_invariant v))"
  unfolding binary_search_pre_def GG_def post_cond_def env_invariant_def
  apply(induction n)
  apply(simp only: case0)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. sorted (arr e) \<and>
                   left e \<le> right e \<and>
                   right e \<le> length (arr e))"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp only: update_left_def)
  apply(intro get_rule; intro allI)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: Suc_leI isSmaller)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def )
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def )
  apply (simp add: isGreater1)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def )
  apply linarith
  apply(simp add: update_val_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply linarith
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def left_Env_def)
  apply auto[1]
  by(simp add: spec_def skip_def)

lemma aux1: "\<lbrakk>(\<exists> i. (i \<le> y \<and> z \<le> i) \<and> xs ! i = v); y < length (xs); z = y\<rbrakk> \<Longrightarrow> xs ! y = v"
  using dual_order.antisym by blast
                                 
lemma main_lemma: "spec (binary_search_pre n v) (BinarySearch n v) (GG (post_cond v))"
  unfolding binary_search_pre_def GG_def post_cond_def update_range_pre_def env_invariant_def
  apply(induction n)
  apply(simp only: case0)
  apply(simp only: spec_def skip_def)
  sledgehammer
   defer
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  defer
  apply(simp add: spec_def skip_def)
  apply linarith

  sorry
end