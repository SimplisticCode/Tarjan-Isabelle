theory Tarjan
imports Main
begin

text \<open>
  Tarjan's algorithm computes the strongly connected components (Loops) of
  a finite graph using depth-first search. 
  This is heavily inspired by the implementation by Stephan Marz that can be found here
  https://homepages.loria.fr/SMerz/projects/tarjan/
\<close>

text \<open>
  Definition of an auxiliary data structure holding local variables
  during the execution of Tarjan's algorithm.
\<close>
record 'v env =
  stack :: "'v list"
  sccs  :: "'v set set"
  sn    :: nat
  num   :: "'v \<Rightarrow> int"
  exploredNotes :: "'v set"

text \<open>
  Definition of a Graph
  A graph has a limit number of vertices and every node can only have a node to other nodes in the graph
\<close>
locale graph =
  fixes vertices :: "'v set"
    and edges :: "'v \<Rightarrow> 'v set"
  assumes vfin: "finite vertices"
    and sclosed: "\<forall>x \<in> vertices. edges x \<subseteq> vertices" 


context graph
begin
text \<open>\<close>
abbreviation edge where
  "edge x y \<equiv> y \<in> edges x"

text \<open>Transitive closure - x can reach itself and if \<close>
inductive reach where
  reach_refl[iff]: "reach x x"
| reach_succ[elim]: "\<lbrakk>edge x y; reach y z\<rbrakk> \<Longrightarrow> reach x z"

lemma reachable_edge: "edge x y \<Longrightarrow> reach x y"
  by auto

lemma reach_is_transitive:
  assumes y: "reach x y" and z: "reach y z"
  shows "reach x z"
  using assms by induct auto


section {* Strongly connected components from the definition of Tarjan*}

definition is_subscc where
  "is_subscc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reach x y"

text\<open>If S is a SCC and S is a subset of S' and S' is a ASK about this\<close>

definition is_scc where
  "is_scc S \<equiv> S \<noteq> {} \<and> is_subscc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subscc S' \<longrightarrow> S' = S)"

lemma sccE:
  \<comment> \<open>Two vertices that are reachable from each other are in the same SCC.\<close>
  assumes "is_scc S" and "x \<in> S"
      and "reach x y" and "reach y x"
  shows "y \<in> S"
  sorry

lemma scc_partition:
  \<comment> \<open>Two SCCs that contain a common element are identical.\<close>
  assumes "is_scc S" and "is_scc S'" and "x \<in> S \<inter> S'"
  shows "S = S'"
  using assms unfolding is_scc_def is_subscc_def
  by (metis IntE assms(2) sccE subsetI)

section \<open>Tarjan's algorithm implementation\<close>

subsection \<open>Function definitions\<close>

function tarjanAlgo where





end