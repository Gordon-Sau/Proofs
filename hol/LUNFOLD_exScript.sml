open pairTheory llistTheory;

Theorem LUNFOLD_Fusion:
  g o f = OPTION_MAP (f ## I) o h ⇒
  LUNFOLD g o f = LUNFOLD h
Proof
QED

Theorem LUNFOLD_I:
  LUNFOLD
  (\l. case l of
       | [||] => NONE
       | (h:::t) => SOME (t,h)) = I
Proof
QED

Theorem o_I_LUNFOLD:
  f o g = I ⇒
  LUNFOLD h o f = LUNFOLD (OPTION_MAP (g ## I) o h o f) 
Proof
QED

