(* *** Walkthrough of the development *)

(* ** Syntax of Martin-Löf Type Theory (MLTT) *)

From LogRel Require Import Notations Utils.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.

Print term.

(* * Fragments for lists *)
(* Type constructor expecting one argument for the parameter type *)
Check tList. 
(* Empty list of a given type *)
Check tNil. 
(* Consing of the head of a list ontop of a tail *)
Check tCons. 
(* Eliminator for lists taking the parameter type, motive,
   hypotheses for empty and cons cases, and main argument list *)
Check tListElim. 

(* Functorial map on lists, taking as arguments its source parameter type A,
  target parameter type B, function f : A -> B and list of type `tList A` *)
Check tMap.


From LogRel Require Import NormalForms UntypedReduction.

(* Inductive presentation of the predicates characterizing the normal
  forms (whnf), neutral forms (whne) and compacted neutral forms (whne_list)
  for weak head reduction *)
Print whnf. 
Check whne : term -> Type.
Check whne_list : term -> Type.

(* In particular, any compacted neutral is a normal form *)
Check whnf_whne_list.
(* and compacted neutrals can either consist of a map of a neutral *)
Check whne_tMap.
(* or simply of a neutral *)
Check whne_list_whne.

(* Weak-head reduction is defined as the transitive closure of 
   the one step weak-head reduction  *)
Print OneRedAlg.

(* Map reduces as expected on canonical forms of lists *)
Check mapNil.
Check mapCons.
(* Moreover, on neutral forms, consecutive maps get compacted *)
Check mapComp.


(* ** Presentations of the typing judgements *)

(* The development employs 3 different presentations of the typing judgements
  for MLTT: 
  - declarative presentation;
  - algorithmic presentation;
  - mixed with algorithmic conversion and declarative typing.

  These presentations all fit into a common interface called the generic typing
  and employed to parametrize the logical relation and the fundamental lemma.
  *)
From LogRel Require Import GenericTyping.

Print GenericTypingProperties.

Print WfContextProperties.
Print WfTypeProperties.
Print TypingProperties.
Print ConvTypeProperties.
Print ConvTermProperties.
Print ConvNeuProperties.
Print ConvNeuListProperties.
Print RedTermProperties.

(* Rules specific to lists *)

About wft_list.
About ty_list.
About ty_nil.
About ty_cons.
About ty_map.
About ty_listElim.

(* Congruence rules for lists *)
About convty_list.
About convtm_list.
About convtm_nil.
About convtm_cons.
About convneu_listElim.
About convneulist_map.

(* * Functor laws in the generic interface *)
(* Identity compaction as a conversion between compacted neutrals *)
About convneulist_map_id.
(* The reduction rules annotate with types
   the untyped weak head reduction relation *)
About redtm_map_comp.


(* * Instances of generic typing *)

From LogRel Require Import DeclarativeTyping DeclarativeInstance AlgorithmicTyping.

(* Declaratve typing *)
Print TypingDecl.

(* Algorithmic conversion *)
Print ConvTypeAlg.

(* Algorithmic typing based on bidirectional typing *)
Print InferAlg.

(* ** Logical Relation *)



(* ** Implementation of the typechecker and conversion checker *)

From PartialFun Require Import Monad PartialFun.
Import IndexedDefinitions.

From LogRel.Decidability Require Import Functions.

About conv.
About typing.


(* Using the results of the logical relation we can prove that the implementation 
  is a correct implementation of (any of the equivalent presentations of) the typing judgement *)

From LogRel.Decidability Require Import Soundness Completeness Termination.

About implem_conv_sound.
About implem_conv_complete.
About conv_terminates.

About implem_typing_sound.
About implem_typing_complete.
About typing_terminates.


(* ** Metatheoretical properties *)
 
From LogRel Require Import Decidability.
 
(* Decidability of typechecking *)
About check_full.

(* Consistency *)

(* Canonicity *)
