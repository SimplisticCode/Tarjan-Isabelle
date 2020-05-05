theory BinarySearch2
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
    put left_Env (mid)
  }"

definition update_right where
  "update_right \<equiv> do{
    mid \<leftarrow> get mid;
    put right_Env (mid)
  }"

text\<open>This method will update either the @{text right} or @{text left} variable, if @{text mid} is not the index that is pointing to @{text val}. If \<close>
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

fun BinarySearch:: "nat  \<Rightarrow> (env, unit) state" where
  case0:"BinarySearch 0  = skip"|
  caseN:"BinarySearch (Suc n) = do {
                        (l, r) \<leftarrow> get (\<lambda>e. (left e, right e));
                        put mid_Env ((r + l) div 2);
                        (if \<not>(r < l) then do{
                          update_range;
                          BinarySearch n
                         }
                       else skip
                      )}"

text\<open>The definiton of how to set up the state-monad/environment with the right values based on an array.\<close>
definition init_env:: "nat list \<Rightarrow> nat \<Rightarrow> env" where
  "init_env l v \<equiv> \<lparr>right = length l,  left = 0, arr = sort(l), mid = (length l + 0) div 2, val = v\<rparr>"

value \<open>snd(run_state (BinarySearch 6) (init_env [0,3,2,1,5,8] 0))\<close>

subsection\<open>Definition of pre- and postcondition\<close>       
text\<open>The array shall be sorted and left is not greater than right\<close>
definition env_invariant:: "env \<Rightarrow> bool" where
"env_invariant e \<equiv> sorted(arr e) \<and> (\<forall>x. x < left e \<and> arr e ! x < val e) \<and> (\<forall>x. x > right e \<and> arr e ! x> val e)"


lemma isSmaller: "(x::nat) < y \<Longrightarrow> (y + x) div 2 < y"
  by linarith

lemma isSmaller1: "(x::nat) < y \<Longrightarrow> Suc((y + x) div 2) \<le> y"
  by linarith

lemma isGreater: "(x::nat) < y \<Longrightarrow> Suc((y + x) div 2) > x"
  by linarith

lemma isGreater1: "(x::nat) < y \<Longrightarrow> ((y + x) div 2) \<ge> x"
  by linarith

lemma update_left_spec: "spec (env_invariant) update_left (GG (env_invariant))"
  unfolding env_invariant_def GG_def
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def left_Env_def)
  by blast

lemma update_right_spec: "spec (env_invariant) update_right (GG (env_invariant))"
  unfolding env_invariant_def GG_def
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def right_Env_def)
  by blast

lemma update_range_spec: "spec (env_invariant) update_range (GG (env_invariant))"
  unfolding  GG_def
  using env_invariant_def spec_def by blast

lemma inv_binarySearch: "spec (env_invariant) (BinarySearch n) (GG (env_invariant))"
  unfolding  GG_def
  apply(induction n rule: BinarySearch.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. env_invariant y)"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def env_invariant_def)
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. env_invariant y)"])
  using env_invariant_def spec_def apply fastforce
  apply blast
  by(simp add: spec_def skip_def)

definition p1:: "env \<Rightarrow> bool" where
"p1 e \<equiv> env_invariant e
          \<and> left e \<le> right e \<and> right e \<le> length(arr e) \<and> mid e = (right e - left e) div 2"

lemma init_env_implies_mid: "e = init_env xs v \<Longrightarrow> mid e = (right e + left e) div 2"
  unfolding  init_env_def
  by simp

lemma empty_range: "(\<forall>i. i > length xs \<and> xs ! i = v)"
  sorry

lemma init_env_implies_p: "e = init_env xs v \<Longrightarrow> env_invariant e"
  unfolding  init_env_def env_invariant_def
  using empty_range by force

lemma init_env_implies_p1: "e = init_env xs v \<Longrightarrow> p1 e"
  unfolding  init_env_def p1_def 
  by (simp add: init_env_def init_env_implies_p)

text\<open>This is the post-condition of binary-search. It is taken from the book "" on page 145.
It basically states that @{text mid} should be a valid index and that if the value we are searching for is inside the array, it should be at position @{text mid}.\<close>
definition q where
"q e \<equiv> left e \<le> mid e \<and> mid e \<le> right e \<and>(arr e ! mid e = val e \<longleftrightarrow> 
  (\<exists>x. x \<ge> left e \<and> x \<le> (right e) \<and> arr e ! x = val e))"

lemma p_implies_q: "p1 e \<Longrightarrow> q e"
  unfolding p1_def q_def
  using env_invariant_def by blast

lemma inv_binarySearch_main: "spec (p1) (BinarySearch n) (GG (p1))"
  unfolding p1_def GG_def
  apply(induction n rule: BinarySearch.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e. env_invariant e \<and>
                   left e \<le> right e \<and>
                   right e \<le> length (arr e) \<and>
                   mid e = (right e - left e) div 2)"])
  apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def env_invariant_def)
  apply blast
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>_ e. env_invariant e \<and>
                   left e \<le> right e \<and>
                   right e \<le> length (arr e) \<and>
                   mid e = (right e - left e) div 2)"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def env_invariant_def)
  apply blast
  apply(simp add: update_right_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply blast
  apply(simp add: spec_def skip_def)
  apply blast
  by(simp add: spec_def skip_def)

text\<open>This lemma states that pre-condition @{text p1} is enough to show that @{text mid} will point to the value we are looking for if it exists in the array. \<close>
lemma binarySearch_main: "spec (p1) (BinarySearch n) (GG (q))"
  unfolding p1_def GG_def q_def
  using env_invariant_def spec_def by blast



end