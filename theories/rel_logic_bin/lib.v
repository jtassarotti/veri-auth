From auth.heap_lang.lib Require Export nondet_bool.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics.
  
Section nondet_bool.
  Context `{!authG Σ}.
  
  Lemma i_nondet_bool (b : bool) E t K :
    nclose specN ⊆ E →
    spec_ideal t (fill K (nondet_bool #())) ={E}=∗
    spec_ideal t (fill K #b).
  Proof.
    iIntros (?) "Hi". rewrite /nondet_bool. 
    i_pures.
    i_alloc as l "Hl".
    i_pures.
    i_fork as j "Hj /=".
    destruct b. 
    - i_pures. by i_load t. 
    - i_store j. i_pures. by i_load t. 
  Qed.
  
End nondet_bool.   

