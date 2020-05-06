theory BinarySearch2
imports 
  Main
  "../State_Monad_HL"
begin

section\<open>Proof Binary Search\<close>
text\<open>This is proof of the binary search algorithm. It is inspired by the proof of the same algorithm in "Verification of Sequential and Concurrent Programs".
     The algorithm is straightforward; it searches recursively after a specific value in a sorted list of numbers. It halves the size of the array it is looking at for each iteration (using the fact that the array is sorted).
     If the number exists in the array it will be found - which in this case means that @{text mid} is the index that is storing the value.\<close>


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

subsubsection\<open>Theorems about how the update functions changes the environment\<close>
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

text\<open>This method will update either the @{text right} or @{text left} variable, if @{text mid} is not the index that is pointing to @{text val}. If @{text mid} is pointing at @{text val} it will do nothing.\<close>
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
                        (if (l < r) then do{
                          update_range;
                          BinarySearch n
                         }
                       else skip
                      )}"

text\<open>The definiton of how to set up the state-monad/environment with the right values based on an array.\<close>
definition init_env:: "nat list \<Rightarrow> nat \<Rightarrow> env" where
  "init_env l v \<equiv> \<lparr>right = length l,  left = 0, arr = sort(l), mid = 0, val = v\<rparr>"

value \<open>snd(run_state (BinarySearch 6) (init_env [0,3,2,1,5,8] 8))\<close>

subsection\<open>Definition of pre- and postcondition\<close>       
text\<open>This method states the invariants of the environment. It is also used as the pre- and post-condition of the function.
    The main thing to note here is that @{text mid} should be a valid index in @{text arr} and all values outside the range of @{text left} and @{text right} should be different (greater or smaller than @{text val}.)\<close>
definition env_invariant:: "env \<Rightarrow> bool" where
"env_invariant e \<equiv> sorted(arr e) \<and> left e \<le> right e \<and> right e \<le> length (arr e) \<and> left e \<le> mid e 
    \<and> mid e \<le> right e  \<and> (\<forall>x:: nat. x < left e \<longrightarrow> arr e ! x < val e) \<and> (\<forall>x. x > right e \<and> x < length (arr e) \<longrightarrow>  arr e ! x> val e)"

text\<open>This is the post-condition of binary-search. It is taken from the book "Verification of Sequential and Concurrent Programs" on page 145.
  It states that the variable @{text mid} should be a valid index in the array
   and that if the value we are searching for is inside the array, it should be at position @{text mid}.\<close>
definition q where
"q e \<equiv> left e \<le> mid e \<and> mid e \<le> right e \<and> (arr e ! mid e = val e \<longrightarrow>
  (\<exists>x. x \<ge> left e \<and> x \<le> right e \<and> x \<le> length (arr e) \<and> arr e  ! x = val e))"

text\<open>The definitions of the pre-condition for each of the three definitions. They are all basically extending the basic pre-condition @{text env_invariant} with the infromation that can be infered from the conditional-statements.\<close>
definition update_range_pre where
"update_range_pre e \<equiv> env_invariant e \<and> mid e = (left e + right e) div 2  \<and> right e > left e"

definition update_left_pre where
"update_left_pre e \<equiv> update_range_pre e \<and> arr e ! mid e < val e"

definition update_right_pre where
"update_right_pre e \<equiv> update_range_pre e \<and> arr e ! mid e > val e"

subsection\<open>Aux lemmas\<close>
text\<open>This lemmas are useful to prove that the update of @{text mid} will still be between @{text left} and @{text right}\<close>
lemma isSmaller: "(x::nat) < y \<Longrightarrow> (y + x) div 2 < y"
  by linarith

lemma isGreater1: "(x::nat) < y \<Longrightarrow> ((y + x) div 2) \<ge> x"
  by linarith

lemma sorted_smaller: "sorted xs \<and>
        m < length xs \<and>
        xs ! m < v \<Longrightarrow>
        (\<forall>x < m. xs ! x < v)"
  by (meson le_less_trans sorted_iff_nth_mono_less)

subsection\<open>Proofs of the definitions\<close>
lemma update_left_spec: "spec (update_left_pre) update_left (GG (env_invariant))"
  unfolding update_range_pre_def env_invariant_def GG_def update_left_pre_def
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def left_Env_def)
  by (metis add.commute sorted_smaller isSmaller less_le_trans)

lemma update_right_spec: "spec (update_right_pre) update_right (GG (env_invariant))"
  unfolding env_invariant_def GG_def update_right_pre_def update_range_pre_def
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro conj_rule_right)
  apply (simp_all add: spec_def put_def put_state_def get_state_def right_Env_def)
  by (metis less_le_trans sorted_iff_nth_mono_less)

lemma update_range_spec: "spec (update_range_pre) update_range (GG (env_invariant))"
  unfolding  GG_def 
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply (smt GG_def Pair_inject case_prodI2 case_prod_conv spec_def update_left_pre_def update_left_spec)
  apply (smt GG_def Pair_inject case_prodI2 case_prod_conv spec_def update_right_pre_def update_right_spec)
  by(simp add: skip_def spec_def env_invariant_def update_range_pre_def)

section\<open>Proof of BinarySearch\<close>
text\<open>This proof shows how it satisfies the invariants on the environment. It is one of the key-proofs.\<close>
lemma inv_binarySearch: "spec (env_invariant) (BinarySearch n) (GG (env_invariant))"
  unfolding  GG_def
  apply(induction n rule: BinarySearch.induct)
  apply(simp add: spec_def skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. env_invariant y \<and> mid y = (left y + right y) div 2)"])
   apply (simp add: spec_def put_def put_state_def get_state_def mid_Env_def env_invariant_def)
  apply linarith
  apply(intro allI)
  apply(intro cond_rule; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. env_invariant y)"])
  apply(simp add: update_range_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: update_left_def)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: env_invariant_def)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply (metis (no_types, hide_lams) add.commute isSmaller leI less_le_trans sorted_smaller)
  apply (simp add: spec_def put_def put_state_def get_state_def left_Env_def)
  apply(simp add: update_right_def)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: env_invariant_def)
  apply(intro conj_rule_right)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)   
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (simp add: spec_def put_def put_state_def get_state_def right_Env_def env_invariant_def)
  apply (metis less_le_trans sorted_iff_nth_mono_less)
  apply(simp add: spec_def skip_def)
  apply blast
  by(simp add: spec_def skip_def)

subsection\<open>Proof of lemma of pre-condition\<close>
text\<open>These proofs show how the @{text init_env} implies/satisfies the invariant on the environment\<close>
lemma empty_range: "(\<forall>i. i > length xs \<and> i \<le> length xs  \<longrightarrow> xs ! i = v)"
  using not_le by blast

lemma init_env_implies_env_inariant: "e = init_env xs v \<Longrightarrow> env_invariant e"
  unfolding init_env_def env_invariant_def
  using empty_range by force

lemma env_inv_implies_q: "env_invariant e \<Longrightarrow> q e"
  unfolding q_def env_invariant_def
  using order_trans by auto

text\<open>This lemma states that pre-condition @{text p1} is enough to show that @{text mid} will point to the value we are looking for if it exists in the array. \<close>
lemma binarySearch_main: "spec (env_invariant) (BinarySearch n) (GG (q))"
  unfolding GG_def
  apply(induction n rule: BinarySearch.induct)
  apply(simp add: spec_def skip_def env_inv_implies_q)
  by (metis GG_def inv_binarySearch env_inv_implies_q strengthen_rule)

text\<open>I can some times be useful to show the correctness of a function using rewriting of the pre-condition to show that the pre-condition and potentially some additional assumptions imply the post-condition. This strategy consists of two proofs:
\begin{enumerate}
\item A proof of the implication from the pre-condition to the post-condition
\item A proof of how the function you want to prove satisfied/keeps the invariant/pre-condition.  
\end{enumerate}

I have also learned some valuable lessons about the use of quantifiers. 
The universal quantifier should always contain an implication, while the existential should use conjunction instead. 
This concerns in this theory the ranges from which the quantified variables are taken from.
\begin{itemize}
\item \<forall>x \<in> A. P(x) is in Isabelle \<forall> x. x \<in> A \<longrightarrow> P(x)
\item \<exists>x \<in> A. P(x) is in Isabelle \<exists> x. x \<in> A /\ P(x) 
\end{itemize}
When working with quantifiers and arrays, it is important to make sure that all variables that are satisfying the predicates of the range are also valid indexes in the array. This does often require an addition predicate about the quantified variable should be in the array (less than the length of the array)

I will also like to add that some algorithms are easier constructed using a syntax that contains a while-loop. \<close>

end