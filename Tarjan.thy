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
          lowlink := (lowlink e) (x := sn e) \<rparr>"
                     
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
                                  
function (domintros) visit:: "'v \<Rightarrow> 'v env  \<Rightarrow> (nat * 'v env)" and dfs_node:: "'v set \<Rightarrow> 'v env \<Rightarrow> (nat * 'v env)"  where 
"visit v e = (let (l1, e1) dfs_node (sucessors v) (add_stack_incr v e) in 
                if l1 \<noteq> (lowlink e) then (l1,e1) (*Lowlink has been changed*)
                else (let (scc, s) split_list v (stack e1) 
            in
              (\<infinity>,            
                \<lparr>stack = s,
                sccs = (set scc) \<union> (sccs e1),     
                sn = sn e1,                              
                lowlink = set_infty scc (lowlink e1),
                exploredNodes = exploredNodes e1\<rparr>)))" and
"dfs_node {} e = (\<infinity>, e)"|                   
"dfs_node neighbours e = (let x = SOME x. x \<in> neightbours;
                            own_LowLink = (if x \<in> exploredNotes then (num e x, e) else visit x e);
                            sibling_LowLink = dfs_node (neighbours - {x}) (snd own_LowLink)       
                            in (min (fst own_LowLink) (fst sibling_LowLink), snd sibling_LowLink))"
                     
(*Get SCC from the environment after performing tarjan*)
definition tarjan where
  "tarjan \<equiv> sccs (snd (dfs_node vertices init_env))"
                                                  
                                    
definition init_env where
  "init_env \<equiv> \<lparr> exploredNotes = {}, stack = [],
                sccs = {},          lowlink = \<lambda>_. 0, 
                sn = 0\<rparr>"
                                    

                              
function tarjan_pre:: "'v \<Rightarrow> 'v env \<Rightarrow> bool" where
"tarjan_pre x e = (card exploredNodes e) = 0 
                   \<and> sn e = 0  \<and> (stack e) = [] \<and> (card sccs e) = 0"
                                      
function tarjan_post:: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env \<Rightarrow> bool" where
"tarjan_post x e = x \<in> vertices 
                    \<and> (card exploredNotes e) = (card vertices)
                    \<and> sn e = (card vertices)"

                             

                                                  
text \<open>How to make invariants?\<close>
(*                                       
  Possible useful invariants could be the stack should always contain only unique elements
  And All The elements in the stack should also be present in the exploredNodes
*)                                                    
definition invariants where          
 "invariants e \<equiv> (\<forall>x set (stack e). x \<in> (exploredNodes e)
                 \<and> card set (stack e) = length (stack e)"
                                                                      
definition exploredNodes_num where
  "exploredNodes_num e \<equiv> \<forall>v \<in> exploredNodes e. v \<in> vertices \<and> num e v > 0"
                                   
                            
text \<open>                          
  The set of nodes explored nodes never decreases in the course
  of the computation.
\<close>
lemma exploredNodes_increasing:


end