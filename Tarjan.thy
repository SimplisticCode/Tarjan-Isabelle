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
  lowlink   :: "'v \<Rightarrow> nat"  \<comment> \<open>Map to keep track of lowlink\<close>
  nodeIndex :: "'v \<Rightarrow> nat"
  exploredNodes :: "'v set"


text \<open>
  Definition of a Graph
  A graph has a finite number of vertices and every node can only have a node to other nodes in the graph
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
                                    
lemma subscc_add:                  
  assumes "is_subscc S" and "x \<in> S"
      and "reach x y" and "reach y x"
  shows "is_subscc (insert y S)"
using assms unfolding is_subscc_def by (metis insert_iff reach_is_transitive)

lemma sccE:
  \<comment> \<open>Two vertices that are reachable from each other are in the same SCC.\<close>
  assumes "is_scc S" and "x \<in> S"
      and "reach x y" and "reach y x"
  shows "y \<in> S"            
using assms unfolding is_scc_def by (metis insertI1 subscc_add subset_insertI)

lemma scc_partition:
  \<comment> \<open>Two SCCs that contain a common element are identical.\<close>
  assumes "is_scc S" and "is_scc S'" and "x \<in> S \<inter> S'"
  shows "S = S'"
  using assms unfolding is_scc_def is_subscc_def
  by (metis IntE assms(2) sccE subsetI)



text \<open>
  Push a vertex on the stack and increment the sequence number.
  The pushed vertex is associated with the (old) sequence number.
\<close>
definition add_stack_incr:: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where 
  "add_stack_incr x e =
      e \<lparr> stack := x # (stack e),
          exploredNodes := {x} \<union> (exploredNodes e),
          sn := sn e + 1,
          lowlink := (lowlink e) (x := sn e), 
          nodeIndex := (nodeIndex e) (x := sn e)\<rparr>"
                     
abbreviation infty ("\<infinity>") where
  \<comment> \<open>nat exceeding any one used as a vertex number during the algorithm\<close>
  "\<infinity> \<equiv> (card vertices)"  

fun split_list:: "'v \<Rightarrow> 'v list \<Rightarrow> ('v list * 'v list)"  where
  "split_list x []  = ([], [])"
| "split_list x (y # xs) =
    (if x = y then ([x], xs) else 
       (let (l, r) = split_list x xs in
         (y # l, r)))" 
           (*
lemma split_list_concat:           
  \<comment> \<open>Concatenating the two sublists produced by @{text "split_list"}
      yields back the original list.\<close>     
  assumes "x \<in> set xs"                 
  shows "(fst (split_list x xs)) @ (snd (split_list x xs)) = xs"
  using assms by (induct xs) (auto simp: split_def)  
                                
 *)
section \<open>Tarjan's algorithm implementation\<close>
                                   
subsection \<open>Function definitions\<close>
                                  
function (domintros) visit and dfs where
  "visit x e  =
    (let (newLowLink, e1) = dfs (edges x) (add_stack_incr x e) in
      if newLowLink < (nodeIndex e x) then (newLowLink, e1)
      else
       (let (scc,rest) = split_list x (stack e1) in
         (\<infinity>, 
           \<lparr> stack = rest,
             sccs = insert (set scc) (sccs e1),
             sn = sn e1,
             lowlink = lowlink e1,
             nodeIndex = nodeIndex e1,
             exploredNodes = exploredNodes e1 \<rparr> )))"
| "dfs roots e =
    (if roots = {} then (\<infinity>, e)
    else
      (let x = SOME x. x \<in> roots;
           \<comment> \<open>If node is unexplored explore it using dfs\<close>
           res1 = (if x \<in> exploredNodes e then (lowlink e x, e) else visit x e);
           res2 = dfs (roots - {x}) (snd res1)
      in (min (fst res1) (fst res2), snd res2) ))" \<comment> \<open>Return lowest lowlink and current env\<close>
  by pat_completeness auto

text\<open>Setup environment\<close>
definition init_env where
  "init_env \<equiv> \<lparr> stack = [],
                sccs = {},           
                sn = 0,
                lowlink = \<lambda>_. 0,
                nodeIndex = \<lambda>_. 0,
                exploredNodes = {}\<rparr>"

(*Get SCC from the environment after performing tarjan*)
definition tarjan where
  "tarjan \<equiv> sccs (snd (dfs vertices init_env))"
                                                                                                                   
definition tarjan_pre:: "'v \<Rightarrow> 'v env \<Rightarrow> bool" where
"tarjan_pre x e \<equiv> exploredNodes e = {} 
                   \<and> sn e = 0  
                   \<and> (stack e) = [] 
                   \<and> card (sccs e) = 0"
                                      
definition tarjan_post:: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env \<Rightarrow> bool" where
"tarjan_post x e e' \<equiv> x \<in> vertices
                    \<and> card (exploredNodes e') = card vertices
                    \<and> sn e' = card vertices"

                             

                                                  
text \<open>How to make invariants?\<close>
(*                                       
  Possible useful invariants could be the stack should always contain only unique elements
  And All The elements in the stack should also be present in the exploredNodes
*)                                                    
definition invariants:: "'v env \<Rightarrow> bool" where          
 "invariants e \<equiv> \<forall>x \<in> set (stack e). x \<in> (exploredNodes e)
                  \<and> distinct (stack e)"
                                                                      
definition exploredNodes_num where
  "exploredNodes_num e \<equiv> \<forall>v \<in> exploredNodes e. v \<in> vertices \<and> nodeIndex e v > 0"
                                   
                            
text \<open>                          
  The set of nodes explored nodes never decreases in the course
  of the computation.
\<close>
lemma exploredNodes_increasing:


end