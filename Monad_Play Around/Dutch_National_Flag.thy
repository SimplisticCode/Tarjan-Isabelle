theory Dutch_National_Flag
imports 
  Main
  "~~/src/HOL/Library/State_Monad"

begin

text\<open>Monad definitions to encode and extract data from the monad\<close>
definition return:: "'a \<Rightarrow> ('b, 'a) state" where "return = State_Monad.return"
definition get:: "(nat list, nat list) state" where "get = State (\<lambda>x. (x,x))"
definition put:: "nat list \<Rightarrow> (nat list, unit) state" where "put x = State (\<lambda>_. ((),x))"
definition skip:: "(nat list, unit) state" where "skip = State (\<lambda>x. ((),x))"


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
      i is the current element being investigated\<close>
fun dnfp:: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp 0 s _ _ _ = s"|
"dnfp (Suc n) s low high i = (if high > i then (if s!i < 1 then (dnfp n (swap s i low) (Suc low) high (Suc i))
                                else (if s!i > 1 then (dnfp n (swap s i (high-1)) low (high-1) i)
                                  else (dnfp n s low high (Suc i))))
                             else s)"

text\<open>A list will always be sorted after run\<close>
lemma "sort(xs) = dnfp (length xs) xs 0 (length xs) 0"
apply(induction xs)
   apply(simp)
  sledgehammer


text\<open>Is this better - with the let and (Suc high)?\<close>
fun dnfp1:: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp1 0 s _ _ _ = s"|
"dnfp1 (Suc n) s low (Suc high) i = (if (Suc high) > i then (
                                  let (xs, l, h, j) = (if s!i < 1 then ((swap s i low), (Suc low), (Suc high), (Suc i))
                                                 else (if s!i > 1 then ((swap s i high), low, high, i)
                                                 else (s, low, (Suc high), (Suc i))))
                                  in (dnfp1 n xs l h j))
                             else s)"

text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
fun dnfp_mon:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat list, unit) state" where
"dnfp_mon 0 _ _ _ = skip"|
"dnfp_mon (Suc n) low high i = (if high > i then 
                                do{
                                  s \<leftarrow> get;
                                  (if s!i < 1 then do {
                                            s \<leftarrow> return(swap s i low);
                                            put s;
                                            dnfp_mon n (Suc low) high (Suc i)
                                          }
                                   else (if s!i > 1 then do
                                          {
                                            s \<leftarrow> return(swap s i (high-1)); 
                                            put s;
                                            dnfp_mon n low (high - 1) i
                                          }
                                       else dnfp_mon n low high (Suc i)))
                                }
                             else skip)"



value \<open>snd(run_state (dnfp_mon 5 0 5 0) [0,2,2,1,2])\<close>
value \<open>snd(run_state (dnfp_mon 9 0 9 0) [0,2,2,0,1,0,2,1,2])\<close>
value \<open>snd(run_state (dnfp_mon 3 0 3 0) [2,1,0])\<close>

value \<open>sorted(snd(run_state (dnfp_mon 5 0 5 0) [0,2,2,1,2]))\<close>
value \<open>sorted(snd(run_state (dnfp_mon 9 0 9 0) [0,2,2,0,1,0,2,1,2]))\<close>
value \<open>sorted(snd(run_state (dnfp_mon 3 0 3 0) [2,1,0]))\<close>


lemma length_dnfp: "length(dnfp n xs k j k) = length xs"
  apply(induction n)
   apply(simp)
    apply(simp add: swap_def length_swap)
  apply(simp)
  sorry

lemma distinct_dnfp[simp]:
  "distinct(dnfp n xs k j k) = distinct xs"
  apply(induction n)
   apply(simp)
  apply(simp only: swap_def distinct_def)
  apply(simp add: rec_list_Cons_imp)
  sorry

fun dnfp_alt:: "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"dnfp_alt [] s _ _ _ _ = s"|
"dnfp_alt (x#xs) s low high i mid = (if high > i then (if s!i < mid then (dnfp_alt xs (swap s i low) (Suc low) high (Suc i) mid)
                                      else (if s!i > mid then (dnfp_alt xs (swap s i (high-1)) low (high-1) i mid)
                                       else (dnfp_alt xs s low high (Suc i) mid))) else s)"


text\<open>How do I evaluate this - where I define a variable/constant and use it in a function call\<close>
value\<open>(xs = [0,0,2,2,1] \<Longrightarrow> (dnfp (length xs) xs 0 (length xs) 1 = [0,0,1,2,2]))\<close>


value\<open>(dnfp 5 [0,0,2,2,1] 0 5 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,0,2,1] 0 8 1)\<close>
value\<open>sorted(dnfp 7 [1,0,2,0,2,2,1] 0 7 1 )\<close>
value\<open>sorted(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1 )\<close>
value\<open>(dnfp 8 [1,0,2,0,2,2,1,0] 0 8 1)\<close>

value\<open>(dnfp1 5 [0,0,2,2,1] 0 5 1) = [0,0,1,2,2]\<close>
value\<open>(dnfp1 8 [1,0,2,0,2,0,2,1] 0 8 1) = [0,0,0,1,1,2,2,2]\<close>
value\<open>sorted(dnfp1 8 [1,0,2,0,2,0,2,1] 0 8 1)\<close>
value\<open>sorted(dnfp1 7 [1,0,2,0,2,2,1] 0 7 1 )\<close>
value\<open>sorted(dnfp1 8 [1,0,2,0,2,2,1,0] 0 8 1 )\<close>
value\<open>(dnfp1 8 [1,0,2,0,2,2,1,0] 0 8 1)\<close>


end