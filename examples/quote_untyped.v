From MetaCoq.Template Require Import All.

Goal True.
Proof.
  quote_term 1 (fun y => pose y).
  quote_utyped_term 1 (fun x => pose x).
