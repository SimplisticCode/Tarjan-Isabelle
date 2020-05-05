theory Insort
imports 
  Main
  "../State_Monad_HL"
  "HOL-Library.Multiset"
begin

record env = 
  high :: "nat"
  low  :: "nat"
  i    :: "nat"
  xs   :: "nat list"


fun insort:: "nat \<Rightarrow> (env, unit) state" where
  case0:"insort 0  = skip"|
  caseN:"insort (Suc n) = do {
                        (arr) \<leftarrow> get (\<lambda>e. (xs e));
                        (if h > j then do{
                          insort n                         
                         }
                       else skip
                      )}"

fun insert:: "nat \<Rightarrow> (env, unit) state" where
  insert_Nil: "insert x = [x]" |
  insert_Cons: "insert x  = do {
                                  
                                  (if x < y then (x#y#ys) else y#insert x ys)}"


primrec insertion_sort:: "nat list \<Rightarrow> (env, unit) state" where
insertion_sort_Nil : "insertion_sort []  = []" |
insertion_sort_Cons: "insertion_sort (x#xs)  = do{ insertion_sort(xs);
                                                    insert x
                                                 }"

end