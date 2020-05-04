theory Dutch_National_Flag_Monad_Definitions
imports 
  Main
  "../State_Monad_HL"
  "HOL-Library.Multiset"
begin

section\<open>Description of the DNFP-algortihm\<close>
text\<open>The Dutch national flag problem is the problem of sorting an array into three different regions: A red-interval (0 in this version), A white-interval (1) and A Blue-interval (2)\<close>

text\<open>The algorithm uses 3 variables to keep track of the three ranges:
\begin{itemize}
  \item @{text Low}: the red range is all indexes before @{text low}
  \item @{text I}: the index that is currently being checked, and the white range is between @{text low} up to @{text i}.
  \item @{text High}: the blue range everything from @{text high} and up.
\end{itemize}

More information about the algorithm can be found: \url{https://en.wikipedia.org/wiki/Dutch_national_flag_problem}

These three ranges have been used as invariants for the algorithm, and all definitions should preserve these.
The relation between the variables has also been described as an invariant.

The main proof of the program is to show the array is sorted in the final state. This can be shown given an array only containing the values of {0,1,2}. The array should also initially satisfy the invariants should be sorted after the termination of the dnfp-function.
\<close>

text\<open>The DNFP-algorithm has been split up in multiple definitions (non-recursive) based on the criteria that a definition should be as simple as possible. 
  A definition shouldn't contain more than a single conditional statement. 
  The simplest definition has been used inside other definitions (see for example, the definition @{text inc_lowbound} that are used inside loop-update-action).
Each of the definitions has been proved individually based on a pre-condition and post-condition.\<close>

text\<open>The pre- and post-conditions are placed in a hierarchy where the conditions from the nested definitions inherit (and strengthen) the conditions from the outer definitions/functions.
    This structure/hierarchy of the pre- a post-conditions makes it possible to use a lot of the already established lemmas of the simple definitions inside the compound definitions.
    To benefit from this, it is essential to first do the proofs of the simple methods before proving the more complicated ones.\<close>

text\<open>A thing to note about the use of the lemmas inside the compound methods is that can't be done if too much rewrite is done - because it makes it impossible for Isabelle to see the relationship between to post-conditions\<close>

text\<open>Some of the pre- and post-conditions take more than one environment as an argument. This is because the post-condition contains some checks about the relation between the variables in the initial and final state (for example, the variable @{text i} is greater in the final state compared to the initial state).
    In this case, it is needed to capture the initial state (as an additional parameter of both the pre- and post-condition) to use it in the post-condition\<close>
section\<open>Proof structure\<close>

text\<open>The proofs are done using the rules defined in the State-Monad-HL. These rules are based on the book 
"Verification of Sequential and Concurrent Programs" and are used to capture changes to the environment.\<close>

text\<open>The proof is built around rewriting an initial state into a final state. 
  The rewriting is done using the rules that capture the meaning of the program\<close>

text\<open>The proofs have all the same structure of a pre-condition that gets turned into a post-condition using the rewrite-rules.
    The strategy for doing this rewriting is, in most cases, as follows:
\begin{enumerate}
  \item Unfold the definitions in the lemma formula (pre- and post-conditions)
  \item Simp to extract the definition of the method
  \begin{itemize}
    \item Get is first - apply the get-rule. 
    \item An all quantifier is first - apply the allI-rule to turn it into an Isabelle Universal Quantifier.
    \item The final state is a conjunction - use the conj-rule-right to prove the goals separately 
    \item Put is first and gets followed by something - use the seq-rule to split it up. The seq rule shall contain what can be concluded from the put.
    \item Put followed by nothing (Usually the case after application of a  seq-rule) - use the simp to discharge the goal. If it doesn't prove the goal, use Sledgehammer, or rewrite the seq-rule.
  \end{itemize}
\end{enumerate}

  The strategy above shall just be repeated until all sub-goals have been proven, and the proof is established. It seems very complicated, but it is, in fact, a very mechanical process.
  In some of the compound methods, the already established lemmas can be used, which means a different strategy should be taken with a lot less rewriting.
\<close>
 
section\<open>Definitions of the monad environment\<close>
type_synonym 'a array = "'a list"

record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat array"

subsection\<open>Monad update functions\<close>
text\<open>Each of the definitions takes an environment and a value of one of the variables. They update the value of the variable and outputs a new environment.\<close>
definition high_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "high_Env s v = s \<lparr> high := v \<rparr>"
definition low_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "low_Env s v = s \<lparr> low := v \<rparr>"
definition i_Env:: "env \<Rightarrow> nat \<Rightarrow> env" where "i_Env s v = s \<lparr> i := v \<rparr>"
definition xs_Env:: "env \<Rightarrow> nat array  \<Rightarrow> env" where "xs_Env s v = s \<lparr> xs := v \<rparr>"

subsection\<open>Theorems about how the update functions changes the environment\<close>
theorem put_high_rule: "spec (\<lambda>x. p () (x \<lparr> high := v \<rparr>)) (put high_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def high_Env_def)

theorem put_low_rule: "spec (\<lambda>x. p () (x \<lparr> low := v \<rparr>)) (put low_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def low_Env_def)

theorem put_i_rule: "spec (\<lambda>x. p () (x \<lparr> i := v \<rparr>)) (put i_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def i_Env_def)

theorem put_xs_rule: "spec (\<lambda>x. p () (x \<lparr> xs := v \<rparr>)) (put xs_Env v) p"
  by (simp add: spec_def put_def get_state_def put_state_def xs_Env_def)

section\<open>Definitions of the methods inside DNFP\<close>
text\<open>This section contains the basic definition of the dnfp-algorithm\<close>

definition swap:: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a array" where
"swap l x y \<equiv> (if x < length l \<and> y < length l then l[x := l!y, y := l!x] else l)"

text\<open>The @{text inc_lowbound} method swaps elements at positions @{text i} and @{text low}. 
    It afterwards increases both @{text i} and @{text low}\<close>
definition inc_lowbound where
"inc_lowbound \<equiv> do{
                  (l, s, j) \<leftarrow> get (\<lambda>e. (low e, xs e, i e));  
                  put xs_Env (swap s j l);
                  j \<leftarrow> get i;                                   
                  put i_Env (Suc j);
                  l \<leftarrow> get low;  
                  put low_Env (Suc l)
                }"

text\<open>The @{text dec_highbound} method first decrements @{text high}. 
    Secondly, it swaps elements at the new position @{text high} with the value at position @{text i}\<close>
definition dec_highbound where
"dec_highbound \<equiv> do{
                    h \<leftarrow> get high;
                    put high_Env (h - 1);
                    (s, j, h) \<leftarrow> get (\<lambda>e. (xs e, i e, high e));
                    put xs_Env (swap s j h)
                }"

text\<open>The @{text inc_index} method increases the variable @{text i}.\<close>
definition inc_index where
"inc_index \<equiv> do{
                  j \<leftarrow> get i;
                  put i_Env (Suc j)
                }"

text\<open>The @{text loop_update_action} method performs a check of the value at position @{text i} and performs one of three actions.\<close>
definition loop_update_action where
"loop_update_action \<equiv> 
  do{
    (s, j) \<leftarrow> get (\<lambda>e. (xs e, i e));
    (if s!j < 1 then do {
      inc_lowbound
    } else (if s!j > 1 then do 
    {
      dec_highbound
    }
   else do {
      inc_index
   }))
  }"

section\<open>Definitions of the invariants\<close>
text\<open>The invariants are taken from \url{https://en.wikipedia.org/wiki/Dutch_national_flag_problem} and more information about them can be seen in the general description of the algorithm.\<close>
text\<open>An insight here is that quantifiers give the best proof-support of list/ranges compared to other list-functions.\<close>
definition low_invariant_is_0_Env where
"low_invariant_is_0_Env e \<equiv> (\<forall>x. x < (low e) \<longrightarrow> (xs e)!x = 0)"

definition invariant_low_to_j_is_1_Env where
"invariant_low_to_j_is_1_Env e \<equiv> (\<forall>x. (x \<ge> (low e) \<and> x < (i e)) \<longrightarrow> (xs e)!x = 1)"

definition high_invariant_is_2_Env where
"high_invariant_is_2_Env e\<equiv> (\<forall>x. x \<ge> (high e) \<and> x < length (xs e) \<longrightarrow> (xs e)!x = 2)"

section\<open>General DNFP conditions\<close>
text\<open>This is the general invariant on the relationship between the variables in the environment.\<close>
definition dnfp_variables_invariants:: "env \<Rightarrow> bool" where
"dnfp_variables_invariants e \<equiv> high e \<ge> i e
                      \<and> i e \<ge> low e 
                      \<and> length (xs e) \<ge> high e
                      \<and> set (xs e) \<subseteq> {0,1,2}"

text\<open>This post-condition states that the variables @{text i}, @{text low}, and the difference between @{text high} and @{text i} will never increase.
    The variable @{text high} will never increase. And the multiset and length of the array will never be changed.\<close>
definition dnfp_post where 
"dnfp_post e e' \<equiv> length (xs e) = length (xs e')
                  \<and> high e \<ge> high e'
                  \<and> low e \<le> low e'
                  \<and> i e \<le> i e'
                  \<and> high e - i e \<ge> high e' - i e'
                  \<and> mset (xs e) = mset (xs e')"

subsection\<open>DNFP invariants\<close>
text\<open>These definitions add the invariant of the relationship with the different invariants on the ranges\<close>
definition dnfp_inv1:: "env \<Rightarrow> bool" where 
"dnfp_inv1  e \<equiv> dnfp_variables_invariants e
                \<and> low_invariant_is_0_Env e"

definition dnfp_inv2:: "env \<Rightarrow> bool" where 
"dnfp_inv2 e \<equiv> dnfp_variables_invariants e
                \<and> invariant_low_to_j_is_1_Env e"

definition dnfp_inv3:: "env \<Rightarrow> bool" where
"dnfp_inv3 e \<equiv> dnfp_variables_invariants e
                \<and> high_invariant_is_2_Env e"

definition dnfp_inv :: "env \<Rightarrow> bool" where
"dnfp_inv e \<equiv> ((dnfp_inv3 e) \<and> (dnfp_inv2 e) \<and> (dnfp_inv1 e))"

subsubsection\<open>Other DNFP spec definitions\<close>
text\<open>This is the final state of the algorithm. The main thing is that @{text i}, @{text high} is equal, and the invariants of the ranges\<close>
definition dnfp_post_final_spec where
"dnfp_post_final_spec e \<equiv> dnfp_inv e \<and> i e = high e"

definition dnfp_mon_spec where
"dnfp_mon_spec e \<equiv> dnfp_variables_invariants e
                    \<and> dnfp_inv e"

definition dnfp_mon_pre::"nat \<Rightarrow> env \<Rightarrow> bool"  where
"dnfp_mon_pre n e \<equiv> dnfp_variables_invariants e \<and> n = high e - i e"

definition i_high_equal::"nat \<Rightarrow> env \<Rightarrow> bool"  where
 "i_high_equal n e \<equiv> high e = i e"

definition dnfp_mon_spec_aux:: "nat \<Rightarrow> env \<Rightarrow> bool" where
"dnfp_mon_spec_aux n e \<equiv> n = high e - i e \<and> dnfp_mon_spec e"

text\<open>This is the main post-condition of the whole theory - the array gets sorted\<close>
definition array_sorted where
"array_sorted e \<equiv> sorted(xs e)"

subsection\<open>Loop update action definitions\<close>
text\<open>These definitions extend the basic definitions of dnfp. An extra assumption extends the preconditions. The assumption can be inferred from the conditions-statement inside the function\<close>
text\<open>The post-condition is also for each of the definitions a little stronger compared to the more general\<close>

definition loop_update_action_pre:: "env \<Rightarrow> bool" where
"loop_update_action_pre e \<equiv> dnfp_variables_invariants e \<and> high e > i e"

text\<open>This is an example of a pre-condition that takes an extra @{text env} as a parameter. This is used to capture the initial state so it can be used in the post-condition.\<close>
definition loop_update_action_pre_aux:: "env \<Rightarrow> env \<Rightarrow> bool" where
"loop_update_action_pre_aux e s \<equiv> s = e
                              \<and> loop_update_action_pre e"

definition loop_update_action_post where
"loop_update_action_post e e' \<equiv> dnfp_post e e'
                                \<and> high e - i e = Suc(high e' - i e')"

subsubsection\<open>Loop update action - Invariants\<close>
definition loop_update_action_inv1:: "env \<Rightarrow> bool" where
"loop_update_action_inv1 e \<equiv> dnfp_inv1 e \<and> loop_update_action_pre e"

definition loop_update_action_inv2:: "env \<Rightarrow> bool" where
"loop_update_action_inv2 e \<equiv> dnfp_inv2 e \<and> loop_update_action_pre e"

definition loop_update_action_inv3:: "env \<Rightarrow> bool" where
"loop_update_action_inv3 e \<equiv> dnfp_inv3 e \<and> loop_update_action_pre e"     

definition loop_update_action_inv :: "env \<Rightarrow> bool" where
"loop_update_action_inv s \<equiv> (dnfp_inv s \<and> loop_update_action_pre s)"

section\<open>Definitions of the methods from inside the conditional-statement inside Loop update action\<close>
text\<open>These definitions rely on the definitions on loop update action (@{text loop_update_action_pre}), but in the precondition they have an extra assumption that gets inferred from the conditions-statement inside loop-update-action\<close>
text\<open>The post-condition does also make the post-condition a little stronger compared to the more general @{text loop_update_action_post}\<close>

subsection\<open>Inc Lowbound definitions\<close>
text\<open>This definitions is just the same as the ones for loop update action, but they are added with the information that can be infered from the conditional-statement. \<close>
definition inc_lowbound_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_pre e s \<equiv> s = e
                        \<and> loop_update_action_pre s
                        \<and> (xs s)!(i s) < 1"

definition inc_lowbound_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_lowbound_post e e'\<equiv> high e = high e'
                          \<and> low e < low e'
                          \<and> loop_update_action_post e e'
                          \<and> i e < i e'"

subsubsection\<open>Inc Index invariants\<close>
text\<open>These invariants is the invariant from the loop-update-action along with the assumption that can be infered from the conditional-statement.\<close>
definition inc_lowbound_inv1:: "env \<Rightarrow> bool" where
"inc_lowbound_inv1 e \<equiv> loop_update_action_inv1 e \<and> xs e ! i e < 1"

definition inc_lowbound_inv2:: "env \<Rightarrow> bool" where
"inc_lowbound_inv2 e \<equiv> loop_update_action_inv2 e \<and> xs e ! i e < 1"

definition inc_lowbound_inv3:: "env \<Rightarrow> bool" where
"inc_lowbound_inv3 e \<equiv> loop_update_action_inv3 e \<and> xs e ! i e < 1"

definition inc_lowbound_inv_pre :: "env \<Rightarrow> bool" where
"inc_lowbound_inv_pre s \<equiv> (loop_update_action_inv s \<and> xs s ! i s < 1)"

subsection\<open>Dec Highbound definitions\<close>
text\<open>This definitions is just the same as the ones for loop update action, but they are added with the information that can be infered from the conditional-statement. \<close>
definition dec_highbound_pre where 
"dec_highbound_pre e s\<equiv> e = s
                        \<and> loop_update_action_pre e 
                        \<and> (xs e)!(i e) > 1"

definition dec_highbound_post where 
"dec_highbound_post e e' \<equiv> length (xs e') > high e' 
                              \<and> high e > high e' 
                              \<and> low e = low e'
                              \<and> i e = i e'
                              \<and> (xs e')!(high e') = 2
                              \<and> loop_update_action_post e e'"

subsubsection\<open>Dec Highbound invariants\<close>
text\<open>These invariants is the invariant from the loop-update-action along with the assumption that can be infered from the conditional-statement.\<close>
definition dec_highbound_inv1:: "env \<Rightarrow> bool" where
"dec_highbound_inv1 e \<equiv> loop_update_action_inv1 e \<and> xs e ! i e > 1"

definition dec_highbound_inv2:: "env \<Rightarrow> bool" where
"dec_highbound_inv2 e \<equiv> loop_update_action_inv2 e \<and> xs e ! i e > 1"

definition dec_highbound_inv3:: "env \<Rightarrow> bool" where
"dec_highbound_inv3 e \<equiv> loop_update_action_inv3 e \<and> xs e ! i e > 1"

definition dec_highbound_inv :: "env \<Rightarrow> bool" where
"dec_highbound_inv s \<equiv> (loop_update_action_inv s \<and> xs s ! i s > 1 )"

subsection\<open>Inc index definitions\<close>
text\<open>This definitions is just the same as the ones for loop update action, but they are added with the information that can be infered from the conditional-statement. \<close>
definition inc_index_pre:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_pre e s \<equiv> e = s 
                      \<and> loop_update_action_pre e
                      \<and> \<not>(xs e)!(i e) > 1
                      \<and> \<not>(xs e)!(i e) < 1"

definition inc_index_post:: "env \<Rightarrow> env \<Rightarrow> bool" where 
"inc_index_post e e' \<equiv> high e = high e' 
                      \<and> low e = low e'
                      \<and> i e < i e'
                      \<and> loop_update_action_post e e'"

subsubsection\<open>Inc index invariants\<close>
text\<open>These invariants is the invariant from the loop-update-action along with the assumption that can be infered from the conditional-statement.\<close>
definition inc_index_inv1:: "env \<Rightarrow> bool" where
"inc_index_inv1 e \<equiv> loop_update_action_inv1 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1"

definition inc_index_inv2:: "env \<Rightarrow> bool" where
"inc_index_inv2 e \<equiv> loop_update_action_inv2 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1"         

definition inc_index_inv3:: "env \<Rightarrow> bool" where
"inc_index_inv3 e \<equiv> loop_update_action_inv3 e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1"

definition inc_index_inv:: "env \<Rightarrow> bool" where
"inc_index_inv e \<equiv> loop_update_action_inv e \<and> \<not>(xs e)!(i e) > 1 \<and> \<not>(xs e)!(i e) < 1"

end