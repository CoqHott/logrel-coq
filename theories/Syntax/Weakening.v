(* Compability file to convert to rasimpl *)
From LogRel.AutoSubst Require Export RAsimpl AstRasimpl.
From LogRel.Syntax Require Export WeakeningDef WeakeningLemmas.

Ltac bsimpl := asimpl.
