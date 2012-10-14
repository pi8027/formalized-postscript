Require Import
  Strings.String ssreflect Common PsCore PsTemplate PsBool PsNat.

Open Scope string.

Eval compute in (pscode_of_inst (proj1_sig exists_instnat_sub)).
Eval compute in (pscode_of_inst (proj1_sig (exists_inst_fill_template 8
  (insttpair (insttpush (insttpush (instthole 2))) (instthole 4))))).
