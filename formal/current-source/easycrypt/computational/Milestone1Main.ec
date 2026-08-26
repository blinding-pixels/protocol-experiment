require import MutationWitnesses.

(* Milestone-only checker entry point. Importing MutationWitnesses forces the
   complete executable dependency closure through the EasyCrypt kernel. The
   public reduction theorems remain reserved for Main.ec. *)
lemma milestone1_dependency_closure_loaded : true.
proof. trivial. qed.
