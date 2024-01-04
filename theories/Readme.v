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
From LogRel Require Import Context Weakening GenericTyping.

Print GenericTypingProperties.

Print WfContextProperties.
Print WfTypeProperties.
Print TypingProperties.
Print ConvTypeProperties.
Print ConvTermProperties.
Print ConvNeuProperties.
Print ConvNeuListProperties.
Print RedTermProperties.

(* Typing rules specific to lists, mostly similar to declarative typing *)

About wft_list.
About ty_list.
About ty_nil.
About ty_cons.
About ty_map.
About ty_listElim.

(* Congruence rules for lists *)
(* As for the other types, constructor have congruence
 rules in conversion *)
About convty_list.
About convtm_list.
About convtm_nil.
About convtm_cons.
(* but destructors only have conversion rules in neutral conversion,
  when their main argument is neutral *)
About convneu_listElim.
About convneulist_map.

(* * Functor laws in the generic interface *)
(* Identity compaction as a conversion between compacted neutrals *)
About convneulist_map_id.
(* The reduction rules annotate with types
   the untyped weak head reduction relation *)
About redtm_map_comp.


(* * Instances of generic typing *)

From LogRel Require Import DeclarativeTyping DeclarativeInstance.
From LogRel Require Import AlgorithmicTyping BundledAlgorithmicTyping AlgorithmicTypingProperties.

(* Declarative typing *)
Print TypingDecl.

(* The generic typing instance for typing *)
About DeclarativeTypingProperties.DeclarativeTypingProperties.

(* Algorithmic conversion *)
Print ConvTypeAlg.

(* Algorithmic typing, based on bidirectional typing *)
Print InferAlg.

(* Bundled typing, algorithmic typing with its pre-conditions *)
Print CheckBun.

(* The last, fully algorithmic instance of generic typing *)
About AlgorithmicTypingProperties.AlgorithmicTypingProperties.

(* ** Logical Relation *)

From LogRel Require Import LogicalRelation Validity Fundamental.
From LogRel.LogicalRelation Require Import Induction Irrelevance Reflexivity Transitivity Weakening Reduction Neutral.
From LogRel.Substitution.Introductions Require Import List ListElim.

Section LogicalRelation.
Context `{GenericTypingProperties}.

(* The logical relation is built from two layers,
  first the reducibility layer attaching witnesses of reducibility to weak-head normal form
  and second the validity layer that closes reducibility under substitution.
*)

(* * Reducibility *)

(* Reducible types are defined with respect to a context Γ and level l *)
Check fun (Γ : context) l (A : term) => [Γ ||-<l> A ].

(* Three predicates are induced by each reducible type A with reducibility witness RA. *)
(* 1) reducible conversion to A *)
Check fun (Γ : context) l (A : term) (RA : [Γ ||-<l> A]) (B : term ) => 
  [Γ ||-<l> A ≅ B| RA].

(* 2) reducibility of terms of type A *)
Check fun (Γ : context) l (A : term) (RA : [Γ ||-<l> A]) (t : term ) => 
  [Γ ||-<l> t : A | RA].

(* 3) reducible conversion of terms of type A *)
Check fun (Γ : context) l (A : term) (RA : [Γ ||-<l> A]) (t u : term ) => 
  [Γ ||-<l> t ≅ u : A | RA].

(* Reducible types are defined inductively, and the seemingly recursive definition 
  of the 3 reducibility predicates is encoded using small-induction recursion:
  the indexed inductive LR relates a syntactic type with a three predicates
  as described above packed in a LRPack *)
Print LRPack.
Print LR.

(* Reducibility is defined for each type former (and the neutrals types).
  We focus on the reducibility of Lists.
  A type `A` is reducible as a list if it weak-head reduces to a term 
  `tList par` where the parameter type `par` is itself reducible
  in any context Δ ≤ Γ (that is, in any weakening of the current context Γ,
  a.k.a. Kripke-style quantification) *)

Print ListRedTy.
(* noted as *)
Check fun Γ l A => [Γ ||-List<l> A].

About ListRedTy.parRed.

(* Reducible conversion to a list type holds for a type `B` when
  `B` weak-head reduces to `tList par'` where `par'` is reducibly convertible
  to `par` *)
Print ListRedTyEq.

About ListRedTyEq.parRed.

(* Reducible terms of list types are defined inductively in two steps:
  - `ListProp` holds of canonical forms of type list (nil, cons and neutrals) with reducible arguments 
  - `ListRedTm` holds of terms that weak-head reduce to a reducible canonical form
  The two inductive definitions must be mutual since the tail of a reducible `cons` need
  not to be in weak-head normal form.
 *)

(* Reducibility of canonical forms of type list *)
Print ListProp.

(* Case nil, the type parameter must be reducibly convertible to that of the 
  reducibility witness of the type *)
About ListRedTm.nilR.

(* Case cons, additionaly to the condition on the type parameter, 
  the head must be reducible at the parameter type, and the tail 
  must be reducible as a term of type list (see below) *)
About ListRedTm.consR.

(* Case neutral, the term must be a well-typed neutral, and if it happens
  to start with a `tMap` additional reducibility information are stored
  in particular with respect to the reducibility of the body of the mapped function *)
About ListRedTm.neR.
Print ListRedTm.map_inv_data.
About ListRedTm.redfn.

(* Reducibility of general terms of type list *)
Print ListRedTm.
Print ListRedTm.red.
Print ListRedTm.prop.

(* Reducible conversion of terms of type list follow a similar pattern to 
  that of terms of type list *)

Print ListPropEq.
About ListRedTmEq.

(* The main subtlety occurs in the comparison of neutrals of list type,
  in order to validate the identity functor law, that is 
  (informally) map id l ~ l for a neutral l of list type.
*)
About ListRedTmEq.neReq.
(* We inspect the head of the two neutrals, and attach additional reducibility information 
  if they start with a `tMap`:
  - if the two terms start with a `tMap`, we are in the congruence case corresponding to the map_inv_data (`map_map_inv_data`)
  - if only one of the two terms starts with a `tMap`, we attach data corresponding to the identity functor law (`map_ne_inv_data`)
*)
Print ListRedTmEq.map_inv_eq.

Print ListRedTmEq.map_map_inv_data.
Print ListRedTmEq.map_ne_inv_data.


(* An induction principle is defined for reducible types, mimicking the inductive-recursive induction principle *)
Print LR_rect_TyUr.

(* This induction principle is then employed to derive a variety of properties
   of reducibility *)

(* An inversion principle *)
Check invLR.
(* In particular, a reducible type `tList A` is reducible as a list type *)
Check invLRList.

(* Irrelevance of the reducibility with respect to reducible conversion *)
Print equivLRPack.
Check LRIrrelevantPack.

(* Irrelevance with respect to universe levels *)
About LRCumulative.

(* Reflexivity, symmetry and transitivity of reducible conversion of types and terms *)
Check LRTyEqRefl_.
Check LREqTermRefl_.

Check LRTyEqSym.
Check LRTmEqSym.

Check LRTransEq.
Check transEqTerm.

(* Closure of reducibility by weakening *)
Check wk.
Check wkTerm.

(* Reducibility is closed by anti-reduction: 
  if a term or type reduces to a reducible term or type, then it is already reducible *)
Check redSubst.
Check redSubstTerm.

(* Finally, neutral terms of reducible types are reducible *)
Print neuTerm. 
Print neuTermEq. 

(* When establishing all these properties, the case of lists need to handle mutually 
  the reducibility of canonical forms and of general terms. 
  For that purpose, we employ derived mutual induction principles. *)
Print ListRedTm.ListRedInduction.
Print ListRedTmEq.ListRedEqInduction.

(* This derived induction principle is used for instance in order to prove 
  transitivity of reducible conversion at list types *)
Locate transEqTermList.

(* * Validity *)

(* Validity closes reducibility by reducible substitution. 
  Valid contexts are described inductively while valid substitutions
  into a valid context and valid conversion of valid substitutions are
  described resursively on these valid contexts.
  As for reducibility, this inductive-recursive schema is encoded
  using small induction-recursion, describing the graph of the function
  relating a valid context with its functions giving the valid substitutions
  and valid convertible substitutions packed into a VPack.
*)
Print VR.
Print VPack.

(* Notations for valid contexts, substitutions, convertible substitutions, types, terms... *)
Check fun Γ => [||-v Γ].
Check fun Γ (VΓ : [||-v Γ]) Δ (wfΔ : [|- Δ]) σ => 
  [VΓ | Δ ||-v σ : Γ | wfΔ]. 
Check fun Γ (VΓ : [||-v Γ]) Δ (wfΔ : [|- Δ]) σ σ' (Vσ : [VΓ | Δ ||-v σ : Γ | wfΔ]) => 
  [VΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | Vσ]. 
Check fun Γ (VΓ : [||-v Γ]) l A => [VΓ | Γ ||-v<l> A].
Check fun Γ (VΓ : [||-v Γ]) l t A (VA : [VΓ | Γ ||-v<l> A]) => 
  [Γ ||-v<l> t : A | VΓ | VA ].

(* The fundamental lemma states that all components of a derivable declarative judgement are valid,
  in particular, terms well-typed for the declarative presentation are valid *)

About Fundamental.
Print FundCon.
Print FundTy.
Print FundTm.
Print FundTyEq.
Print FundTmEq.


(* The proof of the fundamental lemma proceed by an induction on
  declarative typing derivations, using that each declarative derivation step
  is admissible for the validity logical relation. 
  
  These admissibility results are show independently for each type former.
  We focus on the case of lists and the functor laws.
  The proofs follow the description of the logical relation: first, we show
  that each type, term or conversion equation is reducible and then valid.
  *)

(* For canonical forms, reducibility provides the necessary basic blocks *)
About listRed.
About listEqRed.
About nilRed.
About consRed.
About consEqRed.

(* Since canonical forms are stable by substitutions, these proofs extend to validity *)
About listValid.
About listEqValid.
About nilValid.
About consValid.
About consEqValid.


(* For elimination forms (tMap, tListElim), the proof proceed as follow:
  Step 1: the reducibility proof of the main argument is analyzed to reduce to
    the case of a canonical form
  Step 2: the elimination form either reduces on this canonical form to a reducible term or is neutral
  Step 3: in the latter case, the neutral is already reducible
*)

(* Helper functions that computes the result of each eliminator
  form on canonical forms *)
Print mapProp.
Print elimListProp.

About mapRedAux.
About elimListRed_mut.

About mapEqRedAux.

(* One essential ingredient to obtain the functor laws is that 
  composition of functions (e.g. morphisms for list) 
  is definitionally associative and unital
*)
About comp_assoc_app_neutral.
About comp_id_app_neutral.

About mapPropRedCompAux.
About mapPropRedIdAux.

(* Lift to validity *)

About mapValid.
About mapRedConsValid.

About elimListValid.

(* Validity of functor laws *)
About mapRedCompValid.
About mapRedIdValid.


(* Some design choices of the reducibility relation for list 
  are only visible at the level of these proofs. 
  For instance, the fact that the parameter type provided to the `tNil`
  constructor must be reducibly convertible to that of its type 
  is used to apply nilEqRed in elimListRedEq_mut (l.385 of theories/Substitution/Introductions/ListElim.v) *)

End LogicalRelation.


(* ** Implementation of the typechecker and conversion checker *)

From PartialFun Require Import Monad PartialFun.
Import IndexedDefinitions.

From LogRel.Decidability Require Import Functions.

(* The main innovation: the function which compacts a to-be neutral once the reduction machine
has hit a variable *)

About compact.

(* The other functions for conversion and typing, are only extended with the new cases
  related to lists *)

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
 
From LogRel Require Import Decidability Normalisation Consequences.
 
(* Decidability of conversion and typechecking *)
About check_conv.
About check_full.

(* Normalisation *)
About normalisation.
About type_normalisation.

(* Consistency *)
About consistency.

(* Canonicity *)
About nat_canonicity.
