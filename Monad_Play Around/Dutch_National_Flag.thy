theory Dutch_National_Flag
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin
definition swap:: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"swap xs i j \<equiv> (if i < length xs \<and> j < length xs then xs[i := xs!j, j := xs!i] else xs)"

lemma length_swap: "length(swap xs i j) = length xs"
  by(simp add: swap_def)

lemma distinct_swap[simp]:
  "distinct(swap xs i j) = distinct xs"
  by(simp add: swap_def)

value\<open>swap [a,b,c,d,e] 0 4 = [e,b,c,d,a]\<close>

text\<open>The algorithm is constant so n is originally defined as the size of the list.
      s is the list I am sorting
      low is the bound of sorted array
      i is the current element being investigated
      mid is the bound to for adding it two the higher or lower part of the array\<close>
fun dnfp:: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> nat list" where
"dnfp 0 s _ _ _ = s"|
"dnfp n s low high i = (if high > i then (if s!i < 1 then (dnfp (n-1) (swap s i low) (Suc low) high (Suc i))
                                else (if s!i > 1 then (dnfp (n-1) (swap s i (high-1)) low (high-1) i)
                                  else (dnfp (n-1) s low high (Suc i)))) else s)"

fun dnfp_alt:: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp_alt [] s _ _ _ _ = s"|
"dnfp_alt (x#xs) s low high i mid = (if high > i then (if s!i < mid then (dnfp_alt xs (swap s i low) (Suc low) high (Suc i) mid)
                                      else (if s!i > mid then (dnfp_alt xs (swap s i (high-1)) low (high-1) i mid)
                                       else (dnfp_alt xs s low high (Suc i) mid))) else s)"

value\<open>(dnfp_alt [0,0,2,2,1] [0,0,2,2,1] 0 5 1 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp_alt [1,0,2,0,2,0,2,1] [1,0,2,0,2,0,2,1] 0 8 1 1) = [0,0,0,1,1,2,2,2]\<close>

text\<open>How do I evaluate this - where I define a variable/constant and use it in a function call\<close>
value\<open>(\<lbrakk>xs = [0,0,2,2,1]\<rbrakk> \<Longrightarrow> (dnfp (length xs) xs 0 (length xs) 1 = [0,0,1,2,2]))\<close>


value\<open>(dnfp 5 [0,0,2,2,1] 0 5 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1)\<close>
value\<open>sorted(dnfp 7 [1,0,2,0,2,2,1] 0 7 1 )\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1 )\<close>
value\<open>(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1)\<close>



end