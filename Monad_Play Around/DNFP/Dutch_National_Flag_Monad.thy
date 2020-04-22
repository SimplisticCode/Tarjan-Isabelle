theory Dutch_National_Flag_Monad
imports 
  "Dutch_National_Flag_Monad_Definitions_Lemmas"
begin

section\<open>DNFP\<close>
text\<open>A version using a state monad for storing the list/array that is being sorted\<close>
fun dnfp_mon:: "nat \<Rightarrow> (env, unit) state" where
  case0:"dnfp_mon 0  = skip"|
  caseN:"dnfp_mon (Suc n) = do {
                        (h, j) \<leftarrow> get (\<lambda>e. (high e, i e));
                        (if h > j then do{
                          loop_update_action;
                          dnfp_mon n
                         }
                       else skip
                      )}"

section\<open>Lemmas\<close>
subsection\<open>Hoare proofs\<close>
subsection\<open>DNFP_Mon Auxillary lemmas\<close>
lemma dnfp_aux1: "spec (\<lambda>y. length (xs e) = length (xs y)) (dnfp_mon v) (\<lambda>x y. length (xs e) = length (xs y))"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux2: "spec (\<lambda>y. high y \<le> high e) (dnfp_mon v) (\<lambda>x y. high y \<le> high e)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux3: "spec (\<lambda>y. low e \<le> low y) (dnfp_mon v) (\<lambda>x y. low e \<le> low y)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  by (simp add: skip_def)

lemma dnfp_aux4: "spec (\<lambda>y. i e \<le> i y) (dnfp_mon v) (\<lambda>x y. i e \<le> i y)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
      apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply blast
    apply(simp add: spec_def)
  by (simp add: skip_def)

lemma dnfp_aux5: "spec (\<lambda>y. high y - i y \<le> high e - i e) (dnfp_mon v) (\<lambda>x y. high y - i y \<le> high e - i e)"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
   apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply blast
  apply(simp add: spec_def)
  by (simp add: skip_def)

lemma dnfp_aux6: "spec (\<lambda>y. mset (xs e) = mset (xs y)) (dnfp_mon v) (\<lambda>x y. mset (xs e) = mset (xs y))"
  apply(induction v rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply (simp add: skip_def)
  apply(simp only: caseN)
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
  apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply blast
  apply(simp add: spec_def)
  by (simp add: skip_def)

lemma dnfp_aux7: "spec (\<lambda>y. i y \<le> high y \<and> high y - i y \<le> n) (dnfp_mon n) (\<lambda>x y. high y = i y)"
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)    
   apply (simp add: skip_def)    
  apply(simp only: caseN)  
  apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)            
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i y \<le> high y \<and> high y - i y \<le> n)"])
     apply(intro conj_rule_right)              

    apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)        
   apply(intro get_rule; intro allI; simp)             
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i y < high y)"])          
       apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)    
       apply(intro allI; simp)                                    
   apply(intro get_rule; intro allI)                             
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i y \<le> high y)"])     
       apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
       apply(intro allI; simp)                    
     apply(intro get_rule; intro allI)                     
       apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)    
                                 
     apply(simp add: dec_highbound_def)                 
  apply(intro get_rule; intro allI; simp)              
 apply(intro seq_rule[of _ _ "(\<lambda>x y. i y \<le> high y)"])        
     apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
       apply linarith 
         apply(intro allI; simp)            
      apply(intro get_rule; intro allI; simp)                       
     apply(simp add: spec_def put_def xs_Env_def put_state_def get_state_def)
                                         
     apply(simp add: inc_index_def)                
      apply(intro get_rule; intro allI; simp)                       
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)

    apply(intro cond_rule)
      apply(simp add: inc_lowbound_def)                  
      apply(intro get_rule; intro allI; simp)       
(*I need some help here*)                                      
 apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> n \<and> high e = high y \<and> i e = i y)"])          
      apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)    
  defer                               
       apply(intro allI; simp)
  apply(intro get_rule; intro allI)                             
 apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> n)"])   
      apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply linarith                                    
        apply(intro allI; simp)   
    apply(intro get_rule; intro allI)
      apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)    
                                  
      apply(simp add: dec_highbound_def)
      apply(intro get_rule; intro allI; simp)          
(*I need some help here*)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> n)"])
       apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)  

       defer                        
  defer
      apply(simp add: inc_index_def)     
  apply(intro get_rule; intro allI; simp) 
       apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)     
  defer                                   
      apply(intro allI; simp)    
   apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def run_state_def)
  sorry


subsection\<open>DNFP proof\<close>
lemma dnfp_prepost: "spec (dnfp_pre n e) (dnfp_mon n) (GG (dnfp_post e))"
  apply(induction rule: dnfp_mon.induct)
  unfolding dnfp_pre_def dnfp_pre_aux_def GG_def dnfp_post_def
    apply(simp add: spec_def)
   apply (simp add: skip_def)
  apply(intro conj_rule_right; simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
  apply(intro cond_rule)
  apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. length (xs e) = length (xs y))"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
        apply(intro allI; simp)
  using dnfp_aux1 apply blast
        apply(simp add: spec_def skip_def)
   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y \<le> high e)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
       apply(intro allI; simp)
  using dnfp_aux2 apply blast
    apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. low e \<le> low y)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  using dnfp_aux3 apply blast
  apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. i e \<le> i y)"])
    apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  using dnfp_aux4 apply blast
  apply(simp add: spec_def skip_def)

   apply(intro get_rule; intro allI; clarify)
       apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)             
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply (simp add: le_diff_conv)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. high y - i y \<le> high e - i e)"])
       apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
  apply linarith
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
    apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
         apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
  apply linarith
    apply(intro allI; simp)
  using dnfp_aux5 apply blast
  apply(simp add: spec_def skip_def)

 apply(intro get_rule; intro allI; clarify)
 apply(intro cond_rule)
  apply(simp add: loop_update_action_def)
  apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
       apply(intro cond_rule)
 apply(simp add: inc_lowbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
            apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
   apply(intro allI; simp)
   apply(intro get_rule; intro allI)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
         apply(intro get_rule; intro allI)
    apply(simp add: spec_def put_def low_Env_def put_state_def get_state_def)
  apply(simp add: dec_highbound_def)
   apply(intro get_rule; intro allI; simp)
  apply(intro seq_rule[of _ _ "(\<lambda>x y. mset (xs e) = mset (xs y))"])
  apply(simp add: spec_def put_def high_Env_def put_state_def get_state_def)
   apply(intro allI; simp)
  apply(intro get_rule; intro allI; simp)
  apply(simp add: spec_def put_def xs_Env_def swap_def put_state_def get_state_def)
  apply (simp add: Multiset.mset_swap)
  apply(simp add: inc_index_def)
  apply(intro get_rule; intro allI; simp)
   apply(simp add: spec_def put_def i_Env_def put_state_def get_state_def)
    apply(intro allI; simp)
  using dnfp_aux6 apply blast
  by(simp add: spec_def skip_def)

(*
  add precondition:
  Everything outside n is sorted
  high to n
  And finally everything should be sorted
  Post condition high = i 
*)

definition pre_dnfp_mon where
"pre_dnfp_mon n e \<equiv> high e - i e = n
                    \<and> dnfp_precondition e
                    \<and> high e - i e = n
                    \<and> invariants_Env e "

subsection\<open>Invariants proof\<close>
lemma dnfp_invariantRed: "spec (dnfp_inv1) (dnfp_mon n) (GG dnfp_inv1)"
  unfolding dnfp_inv1_def dnfp_pre_aux_def GG_def 
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
   apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> low_invariant_is_0_Env e)"])
    apply(intro cond_rule)
  apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv1_aux_def inc_lowbound_inv1_def inc_lowbound_invariantRed lessI loop_update_action_pre_def prod.simps(1) spec_def)
  apply (smt GG_def case_prodD case_prodI2 dec_highbound_inv1_aux_def dec_highbound_inv1_def dec_highbound_invariantRed loop_update_action_pre_def prod.simps(1) spec_def)
    apply (smt GG_def case_prodD case_prodI2 inc_index_inv1_aux_def inc_index_inv1_def inc_index_invariantRed less_one loop_update_action_pre_def prod.simps(1) spec_def) 
   apply blast
    apply(simp add: spec_def)
   by(simp add: skip_def)

lemma dnfp_invariantWhite: "spec dnfp_inv2 (dnfp_mon n) (GG dnfp_inv2)"
  unfolding dnfp_inv2_def  GG_def dnfp_pre_aux_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> invariant_low_to_j_is_1_Env e)"])
    apply(intro cond_rule; simp)
      apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv2_aux_def inc_lowbound_inv2_def inc_lowbound_invariantWhite lessI loop_update_action_pre_def spec_def)
     apply (smt GG_def One_nat_def case_prodD case_prodI2 dec_highbound_inv2_aux_def dec_highbound_inv2_def dec_highbound_invariantWhite loop_update_action_pre_def spec_def)
  apply (smt GG_def One_nat_def Suc_less_eq inc_index_inv2_aux_def inc_index_inv2_def inc_index_invariantWhite less_Suc_eq loop_update_action_pre_def spec_def split_beta')
  apply blast
    apply(simp add: spec_def)
   by(simp add: skip_def)

lemma dnfp_invariantBlue: "spec dnfp_inv3 (dnfp_mon n) (GG dnfp_inv3)"
  unfolding dnfp_inv3_def dnfp_pre_aux_def  GG_def
  apply(induction n rule: dnfp_mon.induct)
    apply(simp add: spec_def)
    apply(simp add: skip_def)
  apply(simp only: caseN)
   apply(intro get_rule; intro allI; clarify)
  apply(intro cond_rule; simp)
  apply(simp add: loop_update_action_def)
   apply(intro get_rule; intro allI; clarify)
  apply(intro seq_rule[of _ _ "(\<lambda>x e. dnfp_precondition e \<and> high_invariant_is_2_Env e)"])
    apply (intro cond_rule; simp)
      apply (smt GG_def One_nat_def case_prodD case_prodI2 inc_lowbound_inv3_aux_def inc_lowbound_inv3_def inc_lowbound_invariantBlue lessI loop_update_action_pre_def spec_def)
     apply (smt GG_def One_nat_def dec_highbound_inv3_aux_def dec_highbound_inv3_def dec_highbound_invariantBlue loop_update_action_pre_def spec_def split_beta')
  apply (smt GG_def One_nat_def Suc_less_eq inc_index_inv3_aux_def inc_index_inv3_def inc_index_invariantBlue less_Suc_eq loop_update_action_pre_def spec_def split_beta')
 apply blast
     apply(simp add: spec_def)
  by(simp add: skip_def)

 text\<open>Main proof\<close>
definition dnfp_mon_inv :: "env \<Rightarrow> bool" where
"dnfp_mon_inv e \<equiv> ((dnfp_inv3 e) \<and> (dnfp_inv2 e) \<and> (dnfp_inv1 e))"

lemma dnfp_mon_invariants: "spec (dnfp_mon_inv) (dnfp_mon n) (GG dnfp_mon_inv)"
  by (smt GG_def dnfp_invariantBlue dnfp_invariantRed dnfp_invariantWhite dnfp_mon_inv_def invariants_Env_def spec_def split_def)

definition dnfp_post_spec where
"dnfp_post_spec e \<equiv> dnfp_mon_inv e \<and> i e = high e"

lemma dnfp_mon_isSorted: "dnfp_post_spec e \<Longrightarrow> sorted (xs e)" 
  unfolding  dnfp_post_spec_def dnfp_mon_inv_def
  sledgehammer
  by (smt Suc_1 Suc_leD dnfp_inv1_def dnfp_inv2_def dnfp_inv3_def high_invariant_is_2_Env_def invariant_low_to_j_is_1_Env_def less_numeral_extra(1) less_or_eq_imp_le less_trans low_invariant_is_0_Env_def not_less sorted_iff_nth_mono_less)

definition dnfp_post_spec1 where
"dnfp_post_spec1 e \<equiv> dnfp_mon_inv e \<and> i e = high e \<and> sorted(xs e)"

lemma dnfp_mon_main: "spec (dnfp_mon_inv) (dnfp_mon n) (GG (dnfp_post_spec1))"
  unfolding GG_def dnfp_post_spec1_def
  apply(intro conj_rule_right)
    apply (metis GG_def dnfp_mon_invariants strengthen_rule)
   defer
  sorry


end