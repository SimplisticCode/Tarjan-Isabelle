theory Dutch_National_Flag
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin
definition swap:: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
"swap xs i j \<equiv> (if i < length xs \<and> j < length xs then xs[i := xs!j, j := xs!i] else xs)"

lemma length_swap[simp]: "length(swap xs i j) = length xs"
  by(simp add: swap_def)

lemma distinct_swap[simp]:
  "distinct(swap xs i j) = distinct xs"
  by(simp add: swap_def)

value\<open>swap [a,b,c,d,e] 0 4 = [e,b,c,d,a]\<close>


(*How to loo up in a list*)
fun dnfp:: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp [] s _ _ _ _ = s"|
"dnfp (x#xs) s low high i mid = (if high > i then (if s!i < mid then (dnfp xs (swap s i low) (Suc low) high (Suc i) mid)
                                  else (if s!i > mid then (dnfp xs (swap s i high) low (high-1) (Suc i) mid)
                                        else (dnfp xs s low high (Suc i) mid))) else s)"


text\<open>How do I evaluate this - where I define a variable/constant and use it in a function call\<close>
value\<open>\<lbrakk>xs = [0,0,2,2,1]\<rbrakk> \<Longrightarrow> (dnfp xs xs 0 4 0 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp [0,0,2,2,1] [0,0,2,2,1] 0 4 0 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp [1,0,2,0,2,0,2,1] [1,0,2,0,2,0,2,1] 0 8 0 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>(dnfp [1,0,2,0,2,0,2,1] [1,0,2,0,2,0,2,1] 0 8 0 1)\<close>
value\<open>(dnfp [1,0,2,0,2,0,2,1] [1,0,2,0,2,0,2,1] 0 8 0 1)\<close>

value\<open>(dnfp [1,0,2,0,2,2,1] [1,0,2,0,2,2,1] 0 6 0 1)\<close>

value\<open>sorted(dnfp [1,0,2,0,2,0,2,1] [1,0,2,0,2,0,2,1] 0 8 0 1)\<close>
value\<open>sorted(dnfp [1,0,2,0,2,2,1] [1,0,2,0,2,2,1] 0 7 0 1)\<close>
value\<open>sorted(dnfp [1,0,2,0,2,2,1,0] [1,0,2,0,2,2,1,0] 0 7 0 1)\<close>
value\<open>(dnfp [1,0,2,0,2,2,1,0] [1,0,2,0,2,2,1,0] 0 7 0 1)\<close>



end