theory UTP_Monad
  imports   
    "HOL-Library.Monad_Syntax"
begin        

text\<open>This is the small theory developed on direct function from a single state space to set of state space.
It is a monadic function and it fulfills the Monadic-laws (right and left identity) and associativity \<close>

text\<open>All definitions here a postfixed with a number to not interfere with the theory below this.\<close>
type_synonym  ('s, 'a) state_unpacked = "'s \<Rightarrow> ('a \<times> 's) set"
context begin

qualified definition return1 :: "'a \<Rightarrow> ('s, 'a) state_unpacked" where
"return1 a \<equiv> (\<lambda>s. {(a,s)})"

lemma run_state_return1[simp]: "(return1 x) s = {(x, s)}"
  unfolding return1_def
  by simp

text\<open>The two bind functions should formally be similar even though they are defined a little differently. But it seems that it is easier to prove with bind version 2 - because where is limited proof support for set-comprehensions\<close>
qualified definition bind1 :: "('s, 'a) state_unpacked \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state_unpacked) \<Rightarrow> ('s, 'b) state_unpacked" (infixl ">>=" 60) where
  "bind1 f g \<equiv> \<lambda>s. \<Union>{(g (fst x)) (snd x)|x. x \<in> f s}"

qualified definition bind2 :: "('s, 'a) state_unpacked \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state_unpacked) \<Rightarrow> ('s, 'b) state_unpacked" (infixl ">>=" 60) where
  "bind2 f g \<equiv> \<lambda>s. (\<Union>(case_prod g ` (f s)))"

lemma bind1_2_equivalent: "bind1 f g = bind2 f g"
  apply(rule ext)
  unfolding bind2_def bind1_def 
  by auto

lemma bind_left_identity2[simp]: "bind2 (return1 a) f = f a"
unfolding return1_def bind2_def by simp 

lemma bind_right_identity2[simp]: "bind2 m return1 = m"
  apply(rule ext)
  unfolding return1_def bind2_def 
  by simp

lemma bind_left_identity1[simp]: "bind1 (return1 a) f = f a"
unfolding return1_def bind1_def by simp 

lemma bind_right_identity1[simp]: "bind1 m return1 = m"
  by (simp add: bind1_2_equivalent)

lemma bind_assoc1: "bind1 (bind1 m f) g = bind1 m (\<lambda>x. bind1 (f x) g)"
  apply (unfold bind1_def split_def)
  apply (rule ext)
  apply clarsimp
  apply (auto intro: rev_image_eqI)
  by blast


qualified definition get1 :: "('s, 's) state_unpacked" where
"get1 = (\<lambda>s. {(s, s)})"

lemma get_lemma[simp]: "get1 s = {(s, s)}"
unfolding get1_def by simp

qualified definition set1 :: "'s \<Rightarrow> ('s, unit) state_unpacked" where
"set1 s' = (\<lambda>_. {((), s')})"

lemma set_lemma[simp]: "(set1 s') s = {((), s')}"
unfolding set1_def by simp

lemma get_set[simp]: "bind1 get1 set1 = return1 ()"
  unfolding bind1_def get1_def set1_def return1_def
by simp

lemma set_set_lemma[simp]: "bind1 (set1 s) (\<lambda>_. set1 s') = set1 s'"
unfolding bind1_def set1_def
by simp

lemma get_bind_set_rule[simp]: "bind1 get1 (\<lambda>s. bind1 (set1 s) (f s)) = bind1 get1 (\<lambda>s. f s ())"
unfolding bind1_def get1_def set1_def
by simp

lemma get_const_rule[simp]: "bind1 get1 (\<lambda>_. m) = m"
unfolding get1_def bind1_def
by simp


datatype ('s, 'a) state = State (run_state: "'s \<Rightarrow> ('a \<times> 's) set")

definition set_state:: "('s, 'a) state \<Rightarrow> 'a set" where
  "set_state m = {z. (\<exists>s s'. (z, s') \<in> run_state m s)}"

lemma set_state_iff: "x \<in> set_state m \<longleftrightarrow> (\<exists>s s' z. z = x \<and> (z, s') \<in> run_state m s)"
  by (simp add: set_state_def)

definition pred_state:: "('a \<Rightarrow> bool) \<Rightarrow> ('s, 'a) state \<Rightarrow> bool" where
  "pred_state P m \<equiv> (\<forall>s' s. s' \<in> run_state m s \<longrightarrow> P (fst s'))"

lemma pred_stateI[intro]:
  assumes "\<And>a s s'. (a, s') \<in> run_state m s \<Longrightarrow> P a"
  shows "pred_state P m"
  using assms pred_state_def by force


lemma pred_stateD[dest]:
  assumes "pred_state P m" "(a, s') \<in> run_state m s"
  shows "P a"
  using assms(1) assms(2) pred_state_def by force

lemma pred_state_run_state: "pred_state P m \<Longrightarrow> \<forall>s t. t \<in> (run_state m s) \<longrightarrow> P (fst t)"
  by auto

definition state_io_rel :: "('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s, 'a) state \<Rightarrow> bool" where
"state_io_rel P m = (\<forall>s t. t \<in> ((run_state m s)) \<longrightarrow> P s (snd t))"

lemma state_io_relI[intro]:
  assumes "\<And>s t. t \<in> run_state m s \<Longrightarrow> P s (snd t)"
  shows "state_io_rel P m"
  using assms unfolding state_io_rel_def
  by simp

lemma state_io_relD[dest]:
  assumes "state_io_rel P m" "(a, s') \<in> run_state m s"
  shows "P s s'"
  using assms unfolding state_io_rel_def
by (metis snd_conv)

lemma state_io_rel_mono[mono]: "P \<le> Q \<Longrightarrow> state_io_rel P \<le> state_io_rel Q"
  by (metis predicate1I rev_predicate2D state_io_rel_def)

lemma state_ext:
  assumes "\<And>s. run_state m s = run_state n s"
  shows "m = n"
using assms
by (cases m; cases n) auto


text\<open>The return is quite different but I think it shouldn't be compared to the normal definition\<close>
context begin
qualified definition return :: "'a \<Rightarrow> ('s, 'a) state" where
"return a \<equiv> State (\<lambda>s. {(a,s)})"

lemma run_state_return[simp]: "run_state (return x) s = {(x, s)}"
  unfolding return_def
by simp

text\<open>A set-comprehnsion would probably be the way to go here.\<close>
qualified definition ap :: "('s, 'a \<Rightarrow> 'b) state \<Rightarrow> ('s, 'a) state \<Rightarrow> ('s, 'b) state" where
"ap f x = State (\<lambda>s. case run_state f s of s' \<Rightarrow> case (\<Union>{run_state x (snd t) | t. t \<in> s'}) of s'' \<Rightarrow> {((fst g) (fst y), snd(y)) |y g. y \<in> s'' \<and> g \<in> s'})"

lemma run_state_ap[simp]:
  "run_state (ap f x) s = (case run_state f s  of s' \<Rightarrow> case (\<Union>{run_state x (snd t) | t. t \<in> s'}) of s'' \<Rightarrow> {((fst g) (fst y), snd(y)) |y g. y \<in> s'' \<and> g \<in> s'})"
  unfolding ap_def by auto

qualified definition bind :: "('s, 'a) state \<Rightarrow> ('a \<Rightarrow> ('s, 'b) state) \<Rightarrow> ('s, 'b) state" (infixl ">>=" 60) where
(*  "bind f g \<equiv> State(\<lambda>s. \<Union>{run_state (g (fst x)) (snd x)|x. x \<in> (run_state f s)})"*)
  "bind f g = State (bind2 (run_state f) (\<lambda>x. (run_state (g x))))"
text \<open>
  Sometimes it is convenient to write @{text bind} in reverse order.
\<close>

lemma run_state_bind[simp]:
  "run_state (bind x f) s = (case run_state x s of s' \<Rightarrow> \<Union>{run_state (f (fst s'')) (snd s'')|s''. s''\<in> s'})"
  unfolding bind_def bind2_def by auto

adhoc_overloading Monad_Syntax.bind bind

definition
  alternative :: "('s,'a) state \<Rightarrow> ('s,'a) state \<Rightarrow> ('s,'a) state"
  (infixl "OR" 20)
where
  "f OR g \<equiv> State(\<lambda>s. ((run_state f s) \<union> (run_state g s)))"

text \<open>Alternative notation for @{text OR}\<close>
notation (xsymbols)  alternative (infixl "\<sqinter>" 20)

lemma bind_left_identity[simp]: "bind (return a) f = f a"
unfolding return_def bind_def bind2_def by simp 

lemma bind_right_identity[simp]: "bind m return = m"
  apply (unfold bind_def)
  apply(rule state_ext)  
  by (simp add: List_State_Monad.bind2_def cond_case_prod_eta)


definition
  select :: "'a set \<Rightarrow> ('s,'a) state" where
  "select A \<equiv> State (\<lambda>s. (A \<times> {s}))"


text\<open>The bind function is problematic to do proofs with\<close>
lemma bind_assoc[simp]: "bind (bind m f) g = bind m (\<lambda>x. bind (f x) g)"
  apply (unfold bind_def bind2_def)
  by auto


lemma bind_predI[intro]:
  assumes "pred_state (\<lambda>x. pred_state P (f x)) m"
  shows "pred_state P (bind m f)"
apply (rule pred_stateI)
unfolding bind_def bind2_def
  using assms 
  by (metis (mono_tags, lifting) UN_E case_prod_beta fst_conv pred_state_def state.sel)
                                                             
qualified definition get :: "('s, 's) state" where
"get = State (\<lambda>s. {(s, s)})"

lemma run_state_get[simp]: "run_state get s = {(s, s)}"
unfolding get_def by simp

qualified definition set :: "'s \<Rightarrow> ('s, unit) state" where
"set s' = State (\<lambda>_. {((), s')})"

lemma run_state_set[simp]: "run_state (set s') s = {((), s')}"
unfolding set_def by simp

lemma get_set1[simp]: "bind get set = return ()"
  unfolding bind_def get_def set_def return_def bind2_def
by simp

lemma set_set[simp]: "bind (set s) (\<lambda>_. set s') = set s'"
  unfolding bind_def set_def bind2_def
by simp

lemma get_bind_set[simp]: "bind get (\<lambda>s. bind (set s) (f s)) = bind get (\<lambda>s. f s ())"
unfolding bind_def get_def set_def bind2_def
by simp

lemma get_const[simp]: "bind get (\<lambda>_. m) = m"
unfolding get_def bind_def bind2_def
by simp



fun traverse_list :: "('a \<Rightarrow> ('b, 'c) state) \<Rightarrow> 'a list \<Rightarrow> ('b, 'c list) state" where
"traverse_list _ [] = return []" |
"traverse_list f (x # xs) = do {
  x \<leftarrow> f x;
  xs \<leftarrow> traverse_list f xs;
  return (x # xs)
}"

lemma traverse_list_app[simp]: "traverse_list f (xs @ ys) = do {
  xs \<leftarrow> traverse_list f xs;
  ys \<leftarrow> traverse_list f ys;
  return (xs @ ys)
}"
by (induction xs) auto

lemma traverse_comp[simp]: "traverse_list (g \<circ> f) xs = traverse_list g (map f xs)"
by (induction xs) auto

abbreviation mono_state :: "('s::preorder, 'a) state \<Rightarrow> bool" where
"mono_state \<equiv> state_io_rel (\<le>)"

abbreviation strict_mono_state :: "('s::preorder, 'a) state \<Rightarrow> bool" where
"strict_mono_state \<equiv> state_io_rel (<)"

corollary strict_mono_implies_mono: "strict_mono_state m \<Longrightarrow> mono_state m"
  unfolding state_io_rel_def
  using less_le_not_le by blast

lemma return_mono[simp, intro]: "mono_state (return x)"
  by (simp add: state_io_rel_def)

lemma get_mono[simp, intro]: "mono_state get"
  by (simp add: state_io_rel_def)

lemma put_mono:
  assumes "\<And>x. s' \<ge> x"
  shows "mono_state (set s')"
  using assms unfolding set_def
  by (simp add: state_io_rel_def)


qualified definition update :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) state" where
"update f = bind get (set \<circ> f)"

lemma update_id[simp]: "update (\<lambda>x. x) = return ()"
unfolding update_def return_def get_def set_def bind_def bind2_def
by auto

lemma update_comp[simp]: "bind (update f) (\<lambda>_. update g) = update (g \<circ> f)"
unfolding update_def return_def get_def set_def bind_def bind2_def
by auto

lemma set_update[simp]: "bind (set s) (\<lambda>_. update f) = set (f s)"
unfolding set_def update_def bind_def get_def set_def bind2_def
by simp

lemma set_bind_update[simp]: "bind (set s) (\<lambda>_. bind (update f) g) = bind (set (f s)) g"
unfolding set_def update_def bind_def get_def set_def bind2_def
by simp

lemma update_mono:
  assumes "\<And>x. x \<le> f x"
  shows "mono_state (update f)"
using assms unfolding update_def get_def set_def bind_def bind2_def
by (auto intro!: state_io_relI)

lemma update_strict_mono:
  assumes "\<And>x. x < f x"
  shows "strict_mono_state (update f)"
using assms unfolding update_def get_def set_def bind_def bind2_def
by (auto intro!: state_io_relI)

end

end
end