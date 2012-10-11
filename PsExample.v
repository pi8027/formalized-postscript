Require Import
  Strings.String ssreflect Common PsCore PsTemplate PsBool PsNat.

Eval compute in (inst_to_pscode (proj1_sig (exists_instnat_sub))).
Eval compute in (inst_to_pscode (proj1_sig (exists_inst_fill_template 1
  (insttpair (insttpush (insttpush (instthole 2))) (instthole 4))))).
