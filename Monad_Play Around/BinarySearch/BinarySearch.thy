theory BinarySearch
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
  val   :: "nat"


subsection\<open>Monad update functions\<close>
text\<open>Each of the definitions takes an environment and a value of one of the variables. They update the value of the variable and outputs a new environment.\<close>
definition right_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "right_Env s v = s \<lparr> right := v \<rparr>"
definition left_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "left_Env s v = s \<lparr> left := v \<rparr>"
definition arr_Env:: "env \<Rightarrow> nat list  \<Rightarrow> env" where "arr_Env s v = s \<lparr> arr := v \<rparr>"
definition mid_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "mid_Env s v = s \<lparr> mid := v \<rparr>"
definition val_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "val_Env s v = s \<lparr> val := v \<rparr>"

subsection\<open>Theorems about how the update functions changes the environment\<close>
theorem put_right_rule: "spec (\<lambda>x. p () (x \<lparr> right := v \<rparr>)) (put right_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def right_Env_def)

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
    mid \<leftarrow> get mid;
    put left_Env mid
  }"

definition update_right where
  "update_right \<equiv> do{
    mid \<leftarrow> get mid;
    put right_Env mid
  }"


definition update_range where
"update_range \<equiv> do{
                    (mid, xs, v) \<leftarrow> get (\<lambda>e. (mid e, arr e, val e));
                    (if xs ! mid < v then do {
                        update_left  
                    }else (if (xs ! mid > v) then do{
                        update_right
                    }else skip
                    ))
                }"

fun BinarySearch:: "nat \<Rightarrow> (env, unit) state" where
  case0:"BinarySearch 0  = skip"|
  caseN:"BinarySearch (Suc n) = do {
                        (l, r) \<leftarrow> get (\<lambda>e. (left e, right e));
                        put mid_Env ((r + l) div 2);
                        (if r \<noteq> l then do{
                          update_range;
                          BinarySearch n
                         }
                       else skip
                      )}"

text\<open>The definiton of how to set up the state-monad/environment with the right values based on an array.\<close>
definition init_env:: "nat list \<Rightarrow> nat  \<Rightarrow> env" where
  "init_env l v \<equiv> \<lparr>right = length l,  left = 0, arr = sort(l), mid = 0, val = v\<rparr>"

value \<open>snd(run_state (BinarySearch 6) (init_env [0,3,2,1,5,8] 5))\<close>

subsection\<open>Definition of pre- and postcondition\<close>       
text\<open>The array shall be sorted and left is not greater than right\<close>
definition env_invariant:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"env_invariant v e \<equiv> sorted(arr e)
      \<and> left e \<le> right e \<and> right e \<le> length(arr e)"

definition p:: "env \<Rightarrow> bool" where
"p e \<equiv> sorted(arr e)
      \<and> left e \<le> right e \<and> right e \<le> length(arr e)"

definition q where
"q e \<equiv> left e \<le> mid e \<and> mid e \<le> right e \<and> (arr e ! mid e = val e \<longleftrightarrow> 
  (\<exists>x. x \<ge> left e \<and> x < Suc(right e) \<and> arr e ! x = val e))"

definition r1:: "env \<Rightarrow> bool" where
"r1 e \<equiv> sorted(arr e) \<and> arr e ! (mid e) < val e"

definition r2:: "env \<Rightarrow> bool" where
"r2 e \<equiv> sorted(arr e) \<and> arr e ! (mid e) > val e"

definition update_range_pre where
"update_range_pre e  \<equiv> p e \<and> left e < right e \<and> mid e = ((left e + right e) div 2)"

definition update_left_pre where
"update_left_pre e  \<equiv> update_range_pre e  \<and> arr e ! mid e < val e"

definition update_right_pre where
"update_right_pre e \<equiv> update_range_pre e \<and> arr e ! (mid e) > val e"

definition update_left_post where
"update_left_post e \<equiv> r1 e"

definition update_right_post where
"update_right_post e  \<equiv>  r2 e"

text\<open>From page 145\<close>
lemma "p e \<and> mid e = (left e + right e) div 2 \<and> left e = right e \<Longrightarrow> q e"
  unfolding p_def q_def
  using nat_less_le not_less_eq by auto

lemma isSmaller: "(x::nat) < y \<Longrightarrow> (y + x) div 2 < y"
  by linarith

lemma isSmaller1: "(x::nat) < y \<Longrightarrow> Suc((y + x) div 2) \<le> y"
  by linarith

lemma isGreater: "(x::nat) < y \<Longrightarrow> Suc((y + x) div 2) > x"
  by linarith

lemma isGreater1: "(x::nat) < y \<Longrightarrow> ((y + x) div 2) \<ge> x"
  by linarith

lemma aux2:"\<lbrakk>(f::nat) \<le> (l::nat) \<and> m = (f + l) div 2\<rbrakk> \<Longrightarrow>f \<le> m \<and> m \<le> l"
  by linarith

lemma aux3:"\<lbrakk>xs!m < v \<and> l \<le> m \<and> m < r; r < length xs \<and> sorted (xs) \<rbrakk> \<Longrightarrow> 
        ((\<exists>x. x > m \<and> x < r \<and> xs ! x = v) \<longleftrightarrow> (\<exists>x. x \<ge> l \<and> x < r \<and> xs ! x = v))"
  by (metis le_less_trans linear not_less_iff_gr_or_eq sorted_nth_mono)

lemma "p e \<and> mid e = (left e + right e) div 2 \<and> left e \<noteq> right e \<and> arr e ! mid e = val e \<Longrightarrow> q e"
  unfolding p_def q_def
  using aux2 le_imp_less_Suc by blast  

lemma update_left_spec: "spec (update_left_pre) update_left (GG (update_left_post))"
  unfolding update_left_pre_def GG_def update_range_pre_def update_left_post_def p_def r1_def
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  by auto

lemma update_right_spec: "spec (update_right_pre) update_right (GG (update_right_post))"
  unfolding update_right_pre_def GG_def update_range_pre_def update_right_post_def p_def r2_def
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  by auto

definition q_aux where
"q_aux e e2 \<equiv> left e \<le> mid e2 \<and> mid e2 \<le> right e \<and> (arr e ! mid e2 = val e \<longleftrightarrow> 
          (\<exists>x. x \<ge> left e \<and> x < Suc(right e) \<and> arr e ! x = val e))"

definition p_aux :: "nat \<Rightarrow>  env \<Rightarrow> bool" where
"p_aux n e \<equiv>  p e \<and> n = right e - left e \<and> mid e = (left e + right e) div 2"

lemma main_lemma: "spec (p_aux n e) (BinarySearch n) (GG (q_aux e))"
  unfolding p_aux_def q_aux_def p_def GG_def
  apply(induction n)
  apply(simp add: spec_def skip_def)
  using le_less_Suc_eq apply force

  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro conj_rule_right)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e2.
                left e2 \<le> mid e2 )"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def)
  apply linarith
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e2.
                left e2 \<le> mid e2 )"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
     defer
     defer
  apply(intro seq_rule[of _ _ "(\<lambda>_ e2.
                mid e2 \<le> right e2 )"])
apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def)
  apply linarith
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e2.
                mid e2 \<le> right e2 )"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
  defer
  defer
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. (arr y ! mid y = val y) \<longleftrightarrow>
                   (\<exists>x\<ge>left y. x < Suc (right y) \<and> arr y ! x = val y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def)
  sledgehammer
       defer
       apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. (arr y ! mid y = val y) =
                   (\<exists>x\<ge>left y. x < Suc (right y) \<and> arr y ! x = val y))"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
       defer
  defer
  apply linarith

  sorry

definition q1 where
"q1 e \<equiv> p e \<and> mid e = (left e + right e) div 2 \<and> left e = right e"

definition q2 where
"q2 e \<equiv> p e \<and> mid e = (left e + right e) div 2 \<and> left e \<noteq> right e \<and> arr e ! mid e = val e"


definition q3_aux where
"q3_aux e \<equiv> p e \<and> mid e = (left e + right e) div 2 \<and> 
  left e = right e \<longrightarrow> arr e ! mid e \<noteq> val e \<and> 
  left e \<noteq> right e \<longrightarrow> arr e ! mid e = val e"


lemma main_lemma: "spec (p_aux n) (BinarySearch n) (GG (q3_aux))"
  unfolding p_aux_def q3_aux_def GG_def
  apply(induction n)
  apply(simp add: spec_def skip_def p_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro conj_rule_right)

  apply(intro seq_rule[of _ _ "(\<lambda>_ y. p y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def p_def)
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. p y)"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def p_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
       defer
  apply(simp add: spec_def skip_def)
     defer
  apply(intro seq_rule[of _ _ "(\<lambda>x y. right y \<le> length (arr y))"])
apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def)
  apply linarith
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e2.
                mid e2 \<le> right e2 )"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
  defer
  defer
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. (arr y ! mid y = val y) \<longleftrightarrow>
                   (\<exists>x\<ge>left y. x < Suc (right y) \<and> arr y ! x = val y))"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def)
  sledgehammer
       defer
       apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ y. (arr y ! mid y = val y) =
                   (\<exists>x\<ge>left y. x < Suc (right y) \<and> arr y ! x = val y))"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def)
  apply(simp add: spec_def skip_def)
       defer
  defer
  apply linarith

  sorry
end