(** * LogRel.BundledAlgorithmicTyping: algorithmic typing bundled with its pre-conditions, and a tailored induction principle. *)
From Coq Require Import ssrbool List.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening UntypedReduction GenericTyping DeclarativeTyping DeclarativeInstance AlgorithmicTyping DeclarativeSubst TypeConstructorsInj.

Import DeclarativeTypingProperties AlgorithmicTypingData.

(** ** Definition of bundled algorithmic typing *)

(** The idea of these definitions is to put together an algorithmic derivation with the
pre-conditions that ensure it is sensible. Indeed, for instance [Γ |-[al] A] does not
re-check that Γ is well-typed: in the algorithm, this information is instead maintained as
an invariant. But this means that algorithmic variants, do not unconditionally
imply its declarative counterpart, they only do so if their pre-conditions are fulfilled,
eg if the context or type are well-formed. *)

(** Also note that in the case of judgements that “output” a type, ie type inference and
neutral conversion, we allow for an arbitrary conversion to “rectify” the output type.
This makes it easier to handle these in the logical relation, because it means the interface
is stable by arbitrary conversion. *)

(** In the case of a context, there is no judgement, only a pre-condition, as algorithmic
typing never re-checks a context. *)
Record WfContextBun Γ :=
{
  bn_wf_ctx : [|-[de] Γ] ;
}.

Record WfTypeBun Γ A :=
{
  bun_wf_ty_ctx : [|-[de] Γ] ;
  bun_wf_ty : [Γ |-[al] A] ;
}.

Record InferBun Γ A t :=
{
  bun_inf_ctx : [|-[de] Γ] ;
  bun_inf : [Γ |-[al] t ▹ A]
}.

Record InferConvBun Γ A t :=
{
  bun_inf_conv_ctx : [|-[de] Γ] ;
  bun_inf_conv_ty : term ;
  bun_inf_conv_inf : [Γ |-[al] t ▹ bun_inf_conv_ty] ;
  (** Allows to change the type to any convertible one. *)
  bun_inf_conv_conv : [Γ |-[de] bun_inf_conv_ty ≅ A]
}.

Record InferRedBun Γ A t :=
{
  bun_inf_red_ctx : [|-[de] Γ] ;
  bun_inf_red : [Γ |-[al] t ▹h A]
}.

Record CheckBun Γ A t :=
{
  bun_chk_ctx : [|-[de] Γ] ;
  bun_chk_ty : [Γ |-[de] A] ;
  bun_chk : [Γ |-[al] t ◃ A]
}.

Record ConvTypeBun Γ A B :=
{
  bun_conv_ty_ctx : [|-[de] Γ] ;
  bun_conv_ty_l : [Γ |-[de] A] ;
  bun_conv_ty_r : [Γ |-[de] B] ;
  bun_conv_ty : [Γ |-[al] A ≅ B]
}.

Record ConvTypeRedBun Γ A B :=
{
  bun_conv_ty_red_ctx : [|-[de] Γ] ;
  bun_conv_ty_red_l : [Γ |-[de] A] ;
  bun_conv_ty_red_wh_l : isType A ;
  bun_conv_ty_red_r : [Γ |-[de] B] ;
  bun_conv_ty_red_wh_r : isType B ;
  bun_conv_ty_red : [Γ |-[al] A ≅h B]
}.

Record ConvTermBun Γ A t u :=
{
  bun_conv_tm_ctx : [|-[de] Γ] ;
  bun_conv_tm_ty : [Γ |-[de] A] ;
  bun_conv_tm_l : [Γ |-[de] t : A] ;
  bun_conv_tm_r : [Γ |-[de] u : A] ;
  bun_conv_tm : [Γ |-[al] t ≅ u : A]
}.

Record ConvTermRedBun Γ A t u :=
{
  bun_conv_tm_red_ctx : [|-[de] Γ] ;
  bun_conv_tm_red_ty : [Γ |-[de] A] ;
  bun_conv_tm_red_wh_ty : isType A ;
  bun_conv_tm_red_l : [Γ |-[de] t : A] ;
  bun_conv_tm_red_wh_l : whnf t ;
  bun_conv_tm_red_r : [Γ |-[de] u : A] ;
  bun_conv_tm_red_wh_r : whnf u ;
  bun_conv_tm_red : [Γ |-[al] t ≅h u : A]
}.

Record ConvNeuBun Γ A m n :=
{
  bun_conv_ne_ctx : [|-[de] Γ] ;
  bun_conv_ne_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_wh_l : whne m ;
  bun_conv_ne_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_wh_r : whne n ;
  bun_conv_ne : [Γ |-[al] m ~ n ▹ A]
}.

Record ConvNeuRedBun Γ A m n :=
{
  bun_conv_ne_red_ctx : [|-[de] Γ] ;
  bun_conv_ne_red_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_red_wh_l : whne m ;
  bun_conv_ne_red_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_red_wh_r : whne n ;
  bun_conv_ne_red : [Γ |-[al] m ~h n ▹ A]
}.

Record ConvNeuConvBun Γ A m n :=
{
  bun_conv_ne_conv_ctx : [|-[de] Γ] ;
  bun_conv_ne_conv_l : well_typed (ta := de) Γ m ;
  bun_conv_ne_conv_wh_l : whne m ;
  bun_conv_ne_conv_r : well_typed (ta := de) Γ n ;
  bun_conv_ne_conv_wh_r : whne n ;
  bun_conv_ne_conv_ty : term ;
  bun_conv_ne_conv : [Γ |-[al] m ~ n ▹ bun_conv_ne_conv_ty] ;
  bun_conv_ne_conv_conv : [Γ |-[de] bun_conv_ne_conv_ty ≅ A]
}.

Record ConvNeuListBun Γ A m n :=
{
  bun_conv_ne_lst_ctx : [|-[de] Γ] ;
  bun_conv_ne_lst_ty : [Γ |-[de] A] ;
  bun_conv_ne_lst_l : [Γ |-[de] m : tList A] ;
  bun_conv_ne_lst_wh_l : whne_list m ;
  bun_conv_ne_lst_r : [Γ |-[de] n : tList A] ;
  bun_conv_ne_lst_wh_r : whne_list n ;
  bun_conv_ne_lst : [Γ |-[al] m ~ n :List A]
}.

Record RedTypeBun Γ A B :=
{
  bun_red_ty_ctx : [|-[de] Γ] ;
  bun_red_ty_ty : [Γ |-[al] A] ;
  bun_red_ty : [A ⇒* B] ;
}.

Record OneStepRedTermBun Γ A t u :=
{
  bun_osred_tm_ctx : [|-[de] Γ] ;
  (** We do not have the instance yet, so we have to specify it by hand,
  but this really is [Γ |-[bn] t : A]. *)
  bun_osred_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_osred_tm : [t ⇒ u]
}.

Record RedTermBun Γ A t u :=
{
  bun_red_tm_ctx : [|-[de] Γ] ;
  bun_red_tm_tm : typing (ta := bn) (Typing := InferConvBun) Γ A t ;
  bun_red_tm : [t ⇒* u] ;
}.

Record RedTypeBunI Γ A B :=
{
  buni_red_ty_ctx : [|-[de] Γ] ;
  buni_red_ty_ty : [Γ |-[de] A] ;
  buni_red_ty : [A ⇒* B] ;
}.

Record OneStepRedTermBunI Γ A t u :=
{
  buni_osred_tm_ctx : [|-[de] Γ] ;
  buni_osred_tm_tm : [Γ |-[de] t : A] ;
  buni_osred_tm : [t ⇒ u]
}.

Record RedTermBunI Γ A t u :=
{
  buni_red_tm_ctx : [|-[de] Γ] ;
  buni_red_tm_tm : [Γ |-[de] t : A] ;
  buni_red_tm : [t ⇒* u] ;
}.

(** ** Instances *)

(** We actually define two instances, one fully-algorithmic and one where only conversion
is algorithmic, but typing is not. This is needed because we cannot show right away that
(bundled) algorithmic typing has all the properties to be an instance of the generic interface.
The issue is that the logical relation does not give enough properties of neutrals, in particular
we cannot derive that neutral application is injective, ie if [tApp n u] and [tApp n' u'] are
convertible then [n] and [n'] are and so are [u] and [u']. Thus, we use the mixed instance, which
we can readily show, to gather more properties of conversion, enough to show the fully 
algorithmic one. *)

Module BundledTypingData.

  #[export] Instance WfContext_Bundle : WfContext bn := WfContextBun.
  #[export] Instance WfType_Bundle : WfType bn := WfTypeBun.
  #[export] Instance Inferring_Bundle : Inferring bn := InferBun. 
  #[export] Instance InferringRed_Bundle : InferringRed bn := InferRedBun.
  #[export] Instance Typing_Bundle : Typing bn := InferConvBun.
  #[export] Instance Checking_Bundle : Checking bn := CheckBun.
  #[export] Instance ConvType_Bundle : ConvType bn := ConvTypeBun.
  #[export] Instance ConvTypeRed_Bundle : ConvTypeRed bn :=  ConvTypeRedBun.
  #[export] Instance ConvTerm_Bundle : ConvTerm bn := ConvTermBun.
  #[export] Instance ConvTermRed_Bundle : ConvTermRed bn := ConvTermRedBun.
  #[export] Instance ConvNeu_Bundle : ConvNeu bn := ConvNeuBun.
  #[export] Instance ConvNeuRed_Bundle : ConvNeuRed bn := ConvNeuRedBun.
  #[export] Instance ConvNeuConv_Bundle : ConvNeuConv bn := ConvNeuConvBun.
  #[export] Instance ConvNeuList_Bundle : ConvNeuList bn := ConvNeuListBun.
  #[export] Instance RedType_Bundle : RedType bn := RedTypeBun.
  #[export] Instance OneStepRedTerm_Bundle : OneStepRedTerm bn := OneStepRedTermBun.
  #[export] Instance RedTerm_Bundle : RedTerm bn := RedTermBun.

  Ltac fold_bun :=
    change WfContextBun with (wf_context (ta := bn)) in *;
    change WfTypeBun with (wf_type (ta := bn)) in *;
    change InferBun with (inferring (ta := bn)) in * ;
    change InferRedBun with (infer_red (ta := bn)) in * ;
    change InferConvBun with (typing (ta := bn)) in * ;
    change CheckBun with (check (ta := bn)) in * ;
    change ConvTypeBun with (conv_type (ta := bn)) in * ;
    change ConvTermBun with (conv_term (ta := bn)) in * ;
    change ConvNeuBun with (conv_neu (ta := bn)) in * ;
    change ConvTypeRedBun with (conv_type_red (ta := bn)) in * ;
    change ConvTermRedBun with (conv_term_red (ta := bn)) in * ;
    change ConvNeuRedBun with (conv_neu_red (ta := bn)) in *;
    change ConvNeuConvBun with (conv_neu_conv (ta := bn)) in *;
    change ConvNeuListBun with (conv_neu_list (ta := bn)) in *;
    change RedTypeBun with (red_ty (ta := bn)) in * ;
    change OneStepRedTermBun with (osred_tm (ta := bn)) in * ;
    change RedTermBun with (red_tm (ta := bn)) in *.

End BundledTypingData.

Import BundledTypingData.

Module BundledIntermediateData.

  #[export] Instance WfContext_BundleInt : WfContext bni := WfContextDecl.
  #[export] Instance WfType_BundleInt : WfType bni := WfTypeDecl.
  #[export] Instance Typing_BundleInt : Typing bni := TypingDecl.
  #[export] Instance ConvType_BundleInt : ConvType bni := ConvTypeBun.
  #[export] Instance ConvTerm_BundleInt : ConvTerm bni := ConvTermBun.
  #[export] Instance ConvNeuConv_BundleInt : ConvNeuConv bni := ConvNeuConvBun.
  #[export] Instance ConvNeuList_BundleInt : ConvNeuList bni := ConvNeuListBun.
  #[export] Instance RedType_BundleInt : RedType bni := RedTypeBunI.
  #[export] Instance OneStepRedTerm_BundleInt : OneStepRedTerm bni := OneStepRedTermBunI.
  #[export] Instance RedTerm_BundleInt : RedTerm bni := RedTermBunI.

  Ltac unfold_bni :=
    change (wf_context (ta := bni)) with (wf_context (ta := de)) in *;
    change (wf_type (ta := bni)) with (wf_type (ta := de)) in *;
    change (typing (ta := bni)) with (typing (ta := de)) in * ;
    change (conv_type (ta := bni)) with (conv_type (ta := bn)) in * ;
    change (conv_term (ta := bni)) with (conv_term (ta := bn)) in * ;
    change (conv_neu_conv (ta := bni)) with (conv_neu_conv (ta := bn)) in * ;
    change (conv_neu_list (ta := bni)) with (conv_neu_list (ta := bn)) in *.

End BundledIntermediateData.

Set Universe Polymorphism.

Arguments bun_conv_ty {_ _ _}.
Arguments bun_conv_ty_red {_ _ _}.
Arguments bun_conv_tm {_ _ _ _}.
Arguments bun_conv_tm_red {_ _ _ _}.
Arguments bun_conv_ne {_ _ _ _}.
Arguments bun_conv_ne_red {_ _ _ _}.


(* Lemmas on Map *)

Lemma map_eta_well_typed {Γ A t} (r := Map.eta A t):
  [Γ |-[de] t : tList A] ->
  [× [Γ |-[de] r.(Map.tgtTy) ≅ A],
    [Γ |-[de] r.(Map.lst) : tList r.(Map.srcTy)] &
    [Γ ,, r.(Map.srcTy) |-[de] r.(Map.fn) : r.(Map.tgtTy)⟨@wk1 Γ A⟩ ]].
Proof.
  intros Hty.
  assert [Γ |-[de] A] by (eapply list_ty_inv ; boundary).
  assert [Γ |-[de] A ≅ A] by now econstructor.
  assert [Γ,, A |-[de] tRel 0 : A⟨@wk1 Γ A⟩].
  {
    econstructor.
    1: econstructor ; gen_typing.
    rewrite wk1_ren_on ; now econstructor.
  }
  destruct t ; try solve [now split].
  eapply termGen' in Hty as [? [[-> ?? Hfn Hl]]] ; cbn in *.
  split ; tea.
  2: econstructor ; [econstructor|..].
  - now eapply list_ty_inj.
  - erewrite <- wk1_ren_on.
    eapply typing_wk in Hfn ; cbn in * ; tea.
    econstructor ; gen_typing.
  - econstructor.
    2: rewrite wk1_ren_on.
    all: econstructor ; tea.
    gen_typing.
  - replace (_[(tRel 0) ..]) with (t2⟨@wk1 Γ t1⟩).
    replace (_⟨wk1 A⟩) with (t2⟨@wk1 Γ t1⟩) by (now rewrite !wk1_ren_on).
    1: eapply typing_wk.
    + now econstructor.
    + now econstructor ; gen_typing.
    + bsimpl. 
      now renamify.
Qed.

Lemma map_eta_id_conv {Γ t A} (r := Map.eta_id A t):
  [Γ |-[de] t : tList A] ->
  [Γ |-[de] t ≅ tMap r.(Map.srcTy) r.(Map.tgtTy) (tLambda r.(Map.srcTy) r.(Map.fn)) r.(Map.lst) : tList A].
Proof.
  intros.
  symmetry.
  econstructor.
  all: econstructor ; tea.
  eapply list_ty_inv ; boundary.
Qed.

Lemma map_eta_conv {Γ t A} (r := Map.eta A t):
  [Γ |-[de] t : tList A] ->
  [Γ |-[de] t ≅ tMap r.(Map.srcTy) r.(Map.tgtTy) (tLambda r.(Map.srcTy) r.(Map.fn)) r.(Map.lst) : tList A].
Proof.
  intros Hty.
  edestruct (Map.into_view t) as [A' B f l |? ->%Map.is_map_eta] ; cbn ; tea.
  2: now apply map_eta_id_conv.
  pose proof (map_eta_well_typed Hty) as [] ; cbn in *.
  eapply termGen' in Hty as [? [[->]]] ; cbn in *.
  assert [Γ,, A' |-[ de ] tRel 0 : A'⟨↑⟩].
  {
    econstructor.
    all: econstructor ; gen_typing.
  }
  assert [Γ,, A' ,, A'⟨↑⟩ |-[de] tRel 0 : A'⟨↑⟩⟨↑⟩].
  {
    do 2 econstructor.
    all: boundary.
  }
  assert [(Γ,, A'),, A'⟨↑⟩ |-[ de ] f⟨↑⟩⟨upRen_term_term ↑⟩ : arr A'⟨↑⟩⟨↑⟩ B⟨↑⟩⟨↑⟩] as f_wk2.
  {
    replace (f⟨_⟩⟨_⟩) with (f⟨@wk1 (Γ,, A') A'⟨↑⟩ ∘w (@wk1 Γ A')⟩).
    2: now bsimpl.
    eapply typing_meta_conv.
    1: eapply typing_wk ; tea.
    1: boundary.
    rewrite <- wk_comp_ren_on, !wk1_ren_on ; cbn.
    now bsimpl.
  }
  econstructor.
  1: eapply TermMapCong ; refold.
  all: try solve [now econstructor].
  econstructor ; tea.
  - econstructor ; tea.
    now erewrite <- wk1_ren_on.
  - symmetry.
    eapply convtm_meta_conv ; cbn.
    3: reflexivity.
    2: shelve.
    econstructor.
    2: now econstructor.
    econstructor.
    + boundary.
    + econstructor.
      1: boundary.
      now econstructor.
    + eapply typing_meta_conv.
      2: shelve.
      renToWk.
      eapply typing_wk ; tea.
      boundary.
      Unshelve.
      all: now substify ; bsimpl.
    + eapply convtm_meta_conv.
      1: cbn ; econstructor ; tea.
      * boundary.
      * econstructor.
        2: do 2 econstructor ; boundary.
        renToWk.
        eapply typing_meta_conv.
        1: eapply typing_wk ; tea.
        1: rewrite wk1_ren_on ; econstructor ; boundary.
        Unshelve.
        2: exact (B⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩).
        now substify ; cbn ; bsimpl.
      * now bsimpl.
      * now substify ; bsimpl.
Qed.


(** ** Induction principle for bundled algorithmic conversion *)

(** We show an induction principle tailored for the bundled predicates: it threads the invariants
of the algorithm through the derivation, giving us stronger hypothesis in the minor premises,
corresponding to both the pre-conditions being true, and the post-conditions of the induction
hypotheses holding. *)

Section BundledConv.
  Universe u.

  Context (PTyEq PTyRedEq : context -> term -> term -> Type@{u})
  (PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq : context -> term -> term -> term -> Type@{u}).

  (** Rather than writing by hand the various large statements of the induction principles,
  we use Ltac to derive them generically. Hopefully, there is no need to touch any part of
  this code when extending modifying the language with more features. *)
  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTyEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PTyRedEq ?Γ ?A ?B] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> [Γ |-[de] B] -> Hyp)
    | context [PNeEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (well_typed (ta := de) Γ t) -> (well_typed (ta := de) Γ u) -> Hyp)
    | context [PNeRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> (well_typed (ta := de) Γ t) -> (well_typed (ta := de) Γ u) -> Hyp)
    | context [PNeListEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> [Γ |-[de] t : tList A] -> [Γ |-[de] u : tList A] -> Hyp)
    | context [PTmEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
    | context [PTmRedEq ?Γ ?A ?t ?u] =>
        constr:([|-[de] Γ] -> ([Γ |-[de] t : A]) -> ([Γ |-[de] u : A]) -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTyEq ?Γ ?A ?B] =>
        context C [PTyEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PTyRedEq ?Γ ?A ?B] =>
        context C [PTyRedEq Γ A B × [Γ |-[de] A ≅ B]]
    | context C [PNeEq ?Γ ?A ?m ?n] =>
        context C [PNeEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PNeRedEq ?Γ ?A ?m ?n] =>
        context C [PNeRedEq Γ A m n ×
          [× ([Γ |-[de] m ≅ n : A]),
          (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
          (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])]]
    | context C [PNeListEq ?Γ ?A ?t ?u] =>
        context C [PNeListEq Γ A t u × [Γ |-[de] t ≅ u : tList A]]
    | context C [PTmEq ?Γ ?A ?t ?u] =>
        context C [PTmEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | context C [PTmRedEq ?Γ ?A ?t ?u] =>
        context C [PTmRedEq Γ A t u × [Γ |-[de] t ≅ u : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A ≅ ?B] => constr:([Γ |-[bn] A ≅ B])
      | [?Γ |-[al] ?A ≅h ?B] => constr:([Γ |-[bn] A ≅h B])
      | [?Γ |-[al] ?t ≅ ?u : ?A] => constr:([Γ |-[bn] t ≅ u : A])
      | [?Γ |-[al] ?t ≅h ?u : ?A] => constr:([Γ |-[bn] t ≅h u : A])
      | [?Γ |-[al] ?m ~ ?n ▹ ?A] => constr:([Γ |-[bn] m ~ n ▹ A])
      | [?Γ |-[al] ?m ~h ?n ▹ ?A] => constr:([Γ |-[bn] m ~h n ▹ A])
      | [?Γ |-[al] ?m ~ ?n :List ?A] => constr:([Γ |-[bn] m ~ n :List A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  (* Eval cbn beta in ltac:(let T := strong_step (forall (Γ : context) (na' : aname) (A B A' B' : term),
    [Γ |-[ al ] A ≅ A'] ->
    PTyEq Γ A A' ->
    [Γ,, A |-[ al ] B ≅ B'] ->
    PTyEq (Γ,, A) B B' -> PTyRedEq Γ (tProd A B) (tProd na' A' B')) in exact T).
  *)

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  #[local] Definition algo_conv_discipline_stmt := 
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq)) in
      let ind := strong_statement t in
      exact ind).

  (** The main theorem *)
  Theorem algo_conv_discipline : algo_conv_discipline_stmt.
  Proof.
    unfold algo_conv_discipline_stmt; intros.
    apply AlgoConvInduction.
    - intros * HA HB ? IHA' ? ? ?.
      pose proof (HA' := HA).
      pose proof (HB' := HB).
      eapply subject_reduction_type, RedConvTyC in HA', HB' ; tea.
      destruct IHA'.
      1-3: boundary.
      split ; [now eauto|..].
      symmetry in HB'.
      do 2 etransitivity ; tea.
      now econstructor.
    - intros * ? IHA ? IHB ? HP HP'.
      eapply prod_ty_inv in HP as [], HP' as [? HB'].
      assert [Γ,, A |-[de] B'].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now eapply IHA.
      }
      split ; [gen_typing|..].
      destruct IHB as [].
      1-3: gen_typing.
      now econstructor.
    - intros.
      split ; [now eauto|..].
      now gen_typing.
    - intros * ?? _.
      split ; [gen_typing|..].
      now econstructor.
    - intros * ?? _.
      split ; [gen_typing|..].
      now econstructor. 
    - intros * ? IHA ? IHB ? HP HP'.
      eapply sig_ty_inv in HP as [], HP' as [? HB'].
      assert [Γ,, A |-[de] B'].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now eapply IHA.
      }
      split ; [gen_typing|..].
      destruct IHB as [].
      1-3: gen_typing.
      now econstructor.
    - intros * Hconv ih ? hLA hLA'.
      epose proof (list_ty_inv _ _ hLA).
      epose proof (list_ty_inv _ _ hLA').
      split.
      + eauto.
      + constructor. now eapply ih.
    - intros * Hconv IH ? HM HN.
      assert [Γ |-[de] M : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        inversion HM ; subst ; clear HM.
        all: solve [now inversion neM| assumption].
      }
      assert [Γ |-[de] N : U].
      {
        eapply algo_conv_wh in Hconv as [neM neN].
        inversion HN ; subst ; clear HN.
        all: solve [now inversion neN| assumption].
      }
      assert (well_typed (ta := de) Γ M) by now eexists.
      assert (well_typed (ta := de) Γ N) by now eexists.
      split ; [now eauto|..].
      do 2 econstructor.
      all: now apply IH.
    - intros * Hin ? ? _.
      split ; [now eauto|..].
      split.
      + do 2 constructor ; gen_typing.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
      + intros T Hty.
        eapply termGen' in Hty as [? [[? [->]] ?]].
        eapply in_ctx_inj in Hin ; tea ; subst.
        eassumption.
    - intros * ? IHm ? IHt ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      eapply termGen' in Htym' as [? [[? [? [-> Htym']]] ?]].
      eapply termGen' in Htyn' as [? [[? [? [-> Htyn']]] ?]].
      edestruct IHm as [? [IHmc IHm' IHn']].
      1: easy.
      1-2: now econstructor.
      unshelve eapply IHm', prod_ty_inj in Htym' as [].
      unshelve eapply IHn', prod_ty_inj in Htyn' as [].
      edestruct IHt.
      1: easy.
      1-2: now gen_typing.
      split ; [now eauto|..].
      split.
      + econstructor ; gen_typing.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&[-> Htym']) ?]].
        eapply IHm', prod_ty_inj in Htym' as [].
        etransitivity ; [..|eassumption].
        eapply typing_subst1 ; tea.
        now econstructor.
      + intros ? Happ.
        eapply termGen' in Happ as [? [(?&?&[-> Htyn']) ?]].
        eapply IHn', prod_ty_inj in Htyn' as [HA ?].
        etransitivity ; [..|eassumption].
        eapply typing_subst1.
        2: eassumption.
        symmetry in HA.
        now gen_typing.
    - intros * ? IHn ? IHP ? IHz ? IHs ? Hty Hty'.
      pose proof Hty as [? Hty2].
      pose proof Hty' as [? Hty2'].
      eapply termGen' in Hty2 as [? [[->]]].
      eapply termGen' in Hty2' as [? [[->]]].
      edestruct IHn as [? [IHnc IHnty IHnty']].
      1: easy.
      1-2: now eexists.
      assert [|-[de] Γ,, tNat] by boundary.
      assert [Γ,, tNat |-[de] P ≅ P']
        by now edestruct IHP.
      assert [Γ |-[de] hz' : P[tZero..]].
      {
       econstructor ; tea.
       symmetry.
       eapply typing_subst1 ; tea.
       now do 2 econstructor. 
      }
      assert [Γ |-[de] hs' : elimSuccHypTy P].
      {
       econstructor ; tea.
       symmetry.
       now eapply elimSuccHypTy_conv.
      }
      split ; [eauto 10 |..].
      split.
      + now econstructor.
      + now intros ?[? [[->]]]%termGen'.
      + intros ?[? [[->]]]%termGen'.
        etransitivity.
        1: eapply typing_subst1.
        all: eassumption.
    - intros * ? IHe ? IHP ? Hty Hty'.
      pose proof Hty as [? Hty2].
      pose proof Hty' as [? Hty2'].
      eapply termGen' in Hty2 as [? [[->]]].
      eapply termGen' in Hty2' as [? [[->]]].
      edestruct IHe as [? [IHec IHnty IHnty']].
      1: easy.
      1-2: now eexists.
      assert [|-[de] Γ,, tEmpty] by boundary.
      assert [Γ,, tEmpty |-[de] P ≅ P']
        by now edestruct IHP.
      split ; [eauto |..].
      split.
      + now econstructor.
      + now intros ?[? [[->]]]%termGen'.
      + intros ?[? [[->]]]%termGen'.
        etransitivity.
        1: eapply typing_subst1.
        all: eassumption.
    - intros * ? ih ? hm hn.
      pose proof hm as [? [?[[?[?[->]]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      edestruct ih as [? [? ihm ihn]]; tea.
      1,2: now eexists.
      split; [eauto| split].
      + now econstructor.
      + intros ? [?[[?[?[-> []%ihm%sig_ty_inj]]]]]%termGen'.
        etransitivity; tea; now symmetry.
      + intros ? [?[[?[?[-> []%ihn%sig_ty_inj]]]]]%termGen'.
        etransitivity; tea; now symmetry.
    - intros * ? ih ? hm hn.
      pose proof hm as [? [?[[?[?[-> hm']]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      edestruct ih as [? [? ihm ihn]]; tea.
      1,2: now eexists.
      split; [eauto| split].
      + now econstructor.
      + intros ? [?[[?[?[-> h%ihm]]]]]%termGen'.
        pose proof h as []%sig_ty_inj.
        etransitivity; tea.
        eapply typing_subst1; tea; econstructor; eapply TermConv; tea.
        refold; now eapply lrefl.
      + intros ? [?[[?[?[-> h%ihn]]]]]%termGen'.
        pose proof h as []%sig_ty_inj.
        etransitivity; tea.
        eapply typing_subst1; tea; econstructor; eapply TermConv; tea.
    - intros * ? IHm HA ? ? Htym Htyn.
      pose proof Htym as [? Htym'].
      pose proof Htyn as [? Htyn'].
      edestruct IHm as [_ [IHmc IHm' IHn']].
      1: easy.
      1-2: now eexists.
      pose proof (HA' := HA).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: boundary.
      split ; [now eauto|..].
      split.
      + gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
      + intros.
        symmetry in HA'.
        etransitivity ; gen_typing.
    - intros * ? ihlst ? ihfn ? hl hl'.
      pose proof (map_eta_well_typed hl) as [].
      pose proof (map_eta_well_typed hl') as [].
      set (rl := Map.eta B l) in *.
      set (rl' := Map.eta B l') in *.
      assert (well_typed (ta := de) Γ (Map.lst rl)) by now eexists.
      assert (well_typed (ta := de) Γ (Map.lst rl')) by now eexists.
      pose proof ihlst as [? []] ; tea.
      assert [Γ |-[de] A ≅ (Map.srcTy rl)] by (now eapply list_ty_inj).
      assert [Γ |-[de] A ≅ (Map.srcTy rl')] by (now eapply list_ty_inj).
      assert [|-[de] Γ ,, A] by (econstructor ; tea ; boundary).
      assert [Γ,, A |-[de] Map.fn rl : B⟨↑⟩].
      {
        erewrite <- wk1_ren_on.
        econstructor.
        1: eapply stability1 ; last first.
        5: eapply typing_wk.
        1: eassumption.
        all: tea.
        all: boundary.
      }
      assert [Γ,, A |-[de] Map.fn rl' : B⟨↑⟩].
      {
        erewrite <- wk1_ren_on.
        econstructor.
        1: eapply stability1 ; last first.
        5: eapply typing_wk.
        1: eassumption.
        all: tea.
        all: boundary.
      }
      split ; eauto.
      etransitivity.
      1: eapply map_eta_conv ; tea.
      etransitivity.
      2: symmetry ; eapply map_eta_conv ; tea.
      econstructor.
      1: eapply TermMapCong ; refold.
      + etransitivity ; tea.
        now symmetry.
      + etransitivity ; tea.
        now symmetry.
      + fold rl rl'.
        assert [Γ |-[ de ] Map.tgtTy rl ≅ Map.tgtTy rl'].
        {
          etransitivity ; tea.
          now symmetry.
        }
        eapply lambda_cong ; tea.
        * boundary.
        * boundary.
        * renToWk.
          eapply typing_wk.
          1: boundary.
          econstructor ; boundary.
        * eapply typing_meta_conv ; tea.
          now bsimpl.
        * etransitivity ; tea.
          now symmetry.
        * rewrite wk1_ren_on.
          renToWk.
          eapply typing_wk ; tea.
          econstructor ; boundary.
        * econstructor.
          1: eapply stability1.
          4: eapply ihfn.
          all: tea.
          1-2: boundary.
          1: now symmetry.
          symmetry.
          renToWk.
          eapply typing_wk ; tea.
          now econstructor ; boundary.
      + econstructor ; tea.
        now econstructor.
      + now econstructor. 
    - intros * HA Ht Hu ? IH ? Htyt Htyu.
      pose proof (HA' := HA).
      pose proof (Ht' := Ht).
      pose proof (Hu' := Hu).
      eapply subject_reduction_type, RedConvTyC in HA'.
      2: boundary.
      eapply subject_reduction, RedConvTeC in Ht' ; tea.
      eapply subject_reduction, RedConvTeC in Hu' ; tea.
      pose proof (Ht'' := Ht').
      pose proof (Hu'' := Hu').
      eapply boundary in Ht'' as [], Hu'' as [].
      split ; [now gen_typing|..].
      etransitivity ; [..|etransitivity].
      1: eassumption.
      2: now symmetry.
      econstructor.
      2: now symmetry.
      eapply IH.
      all: gen_typing.
    - intros * ? IHA ? IHB ? Hty Hty'.
      pose proof (Htyd := Hty).
      pose proof (Htyd' := Hty').
      eapply termGen' in Htyd as [? [[->] _]].
      eapply termGen' in Htyd' as [? [[->] _]].
      assert [Γ,, A |-[de] B' : U].
      { eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        now econstructor.
      }
      split ; [now gen_typing|..].
      econstructor.
      + assumption.
      + now eapply IHA.
      + now eapply IHB ; gen_typing.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHt ? Htyt Htyt'.
      pose proof (Htyd := Htyt).
      pose proof (Htyd' := Htyt').
      eapply termGen' in Htyd as [? [[->] _]].
      eapply termGen' in Htyd' as [? [[->] _]].
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; eauto.
      now econstructor. 
    - intros * ? ? ? IH ? Hf Hg.
      assert [Γ |-[de] A] by
        (now eapply boundary, prod_ty_inv in Hf).
      pose proof (Hf' := Hf).
      pose proof (Hg' := Hg).
      eapply typing_eta' in Hf'.
      eapply typing_eta' in Hg'.
      split ; [now gen_typing|..].
      econstructor ; tea.
      now eapply IH ; gen_typing.
    - intros * ? ihA ? ihB ? hty hty'.
      pose proof hty as [?[[->]]]%termGen'.
      pose proof hty' as [?[[->]]]%termGen'.
      edestruct ihA as []; tea.
      edestruct ihB as []; tea.
      1: gen_typing.
      1: eapply stability1; tea; gen_typing.
      split ; [eauto|now econstructor].
    - intros * ??? ihfst ? ihsnd ? hp hq.
      edestruct ihfst as []; tea.
      1,2: now econstructor.
      pose proof hp as []%boundary%sig_ty_inv.
      edestruct ihsnd as []; tea.
      1: now econstructor.
      2: split; [eauto|now econstructor].
      eapply wfTermConv; [now econstructor|].
      eapply typing_subst1; [now symmetry|].
      now eapply TypeRefl.
    - intros * ? ih ? hLA hLA'.
      destruct (termGen' _ _ _ hLA) as [? [[->]]].
      destruct (termGen' _ _ _ hLA') as [? [[->]]].
      split. 2: now constructor.
      eauto.
    - intros * ? hnil hnil'.
      destruct (termGen' _ _ _ hnil) as [? [[-> ?] c]].
      destruct (termGen' _ _ _ hnil') as [? [[->]]].
      pose proof c as [_ ?%list_ty_inv]%boundary.
      split; [eauto|].
      econstructor. 
      1:{ 
        eapply TermNilCong; refold.
        etransitivity; eapply list_ty_inj; tea.
        now symmetry.
      }
      tea.
    - intros * ? ihhd ? ihtl ? hcons hcons'.
      destruct (termGen' _ _ _ hcons) as [? [[-> ?] c]].
      destruct (termGen' _ _ _ hcons') as [? [[->]]].
      assert [Γ |-[de] A ≅ AT] as eq by now eapply list_ty_inj.
      assert [Γ |-[de] A' ≅ AT] as eq' by now eapply list_ty_inj.
      assert [Γ |-[de] AT] by now apply boundary in eq.
      assert [Γ |-[de] hd : AT] by now econstructor.
      assert [Γ |-[ de ] hd' : AT] by now econstructor.
      assert [Γ |-[de] tl : tList AT]
        by (econstructor ; tea ; now econstructor).
        assert [Γ |-[de] tl' : tList AT]
          by (econstructor ; tea ; now econstructor).
      destruct ihhd, ihtl; tea.
      split.
      1: eauto 10.
      econstructor.
      1:eapply TermConsCong; refold; tea.
      + etransitivity ; tea ; now symmetry.
      + econstructor ; tea.
        now symmetry.
      + econstructor ; tea.
        econstructor.
        now symmetry.
      + now econstructor.    
    - intros * ? IH **.
      split ; eauto.
      now destruct IH.
    - intros * ? IHm ? ? Htym Htyn.
      edestruct IHm as [? [? Hm']].
      1: easy.
      1-2: now eexists.
      split ; [now eauto|..].
      econstructor ; tea.
      now eapply Hm'.
  Qed. 

  Definition BundledConvInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq) in
      let t' := weak_statement t in exact t').

  (** As a corollary, we get the desired induction principle. The difference with the above one
  is that we do not get the post-condition of the algorithm in the conclusion, but this is
  in general not necessary. *)
  Corollary BundledConvInduction :
    ltac:(
      let t := (type of (AlgoConvInduction PTyEq PTyRedEq PNeEq PNeRedEq PNeListEq PTmEq PTmRedEq)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat split.
    all: intros * [].
    all: apply algo_conv_discipline ; assumption.
  Qed.

End BundledConv.

(** ** Soundness of algorithmic conversion *)

(** Contrarily to the induction principle above, if we instantiate the main principle with
only constant true predicates, we get only the post-conditions, ie a soundness theorem: bundled algorithmic conversion judgments imply their declarative counterparts. *)

Section ConvSoundness.

  Let PTyEq (Γ : context) (A B : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] B] ->
    [Γ |-[de] A ≅ B].
  Let PTmEq (Γ : context) (A t u : term) :=
    [Γ |-[de] t : A] -> [Γ |-[de] u : A] ->
    [Γ |-[de] t ≅ u : A].
  Let PNeEq (Γ : context) (A : term) (m n : term) :=
    (well_typed (ta := de) Γ m) ->
    (well_typed (ta := de) Γ n) ->
    [× [Γ |-[de] m ≅ n : A],
      (forall T, [Γ |-[de] m : T] -> [Γ |-[de] A ≅ T]) &
      (forall T, [Γ |-[de] n : T] -> [Γ |-[de] A ≅ T])].
  Let PNeListEq (Γ : context) (A t u : term) :=
    [Γ |-[de] t : tList A] -> [Γ |-[de] u : tList A] ->
    [Γ |-[de] t ≅ u : tList A].

  Theorem algo_conv_sound : AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PNeListEq PTmEq PTmEq.
  Proof.
    subst PTyEq PTmEq PNeEq PNeListEq.
    red.
    pose proof (algo_conv_discipline 
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ _ => True))
    as [H' H] ;
    cycle -1.
    1:{
      repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : well_typed _ _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
      intros ; apply H ; gen_typing. }
    all: now constructor.
  Qed.

End ConvSoundness.

Theorem bn_conv_sound :
BundledConvInductionConcl
  (fun Γ A B => [Γ |-[de] A ≅ B])
  (fun Γ A B => [Γ |-[de] A ≅ B])
  (fun Γ A t u => [Γ |-[de] t ≅ u : A])
  (fun Γ A t u => [Γ |-[de] t ≅ u : A])
  (fun Γ A t u => [Γ |-[de] t ≅ u : tList A])
  (fun Γ A t u => [Γ |-[de] t ≅ u : A])
  (fun Γ A t u => [Γ |-[de] t ≅ u : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_conv_sound in H end.
  all: prod_hyp_splitter.
  all: eassumption.
Qed.

Theorem bn_ne_conv_sound Γ A n n' :
  [Γ |-[bn] n ~ n' : A] ->
  [Γ |-[de] n ≅ n' : A].
Proof.
  intros [?????? []%algo_conv_sound ?] ; tea.
  now econstructor.
Qed.

(** ** Inductive presentation of bundled algorithmic conversion *)

  Inductive ConvTypeBunAlg : forall {Γ A B}, ConvTypeAlg Γ A B -> Type :=
  | typeConvRedBun {Γ A A' B B'}
      (redA : [A ⇒* A'])
      (redB : [B ⇒* B'])
      (conv : [Γ |-[bn] A' ≅h B']) :
      ConvTypeBunAlg (typeConvRed redA redB conv.(bun_conv_ty_red)).
  
  Lemma bun_conv_ty_inv {Γ A B} (conv : [Γ |-[bn] A ≅ B]) :
    ConvTypeBunAlg conv.(bun_conv_ty).
  Proof.
    destruct conv as [? hA hB convA].
    destruct convA as [????? redA redB conv]; cbn. 
    eapply subject_reduction_type, RedConvTyC in hA, hB ; tea.
    pose proof (fst (snd algo_conv_wh) _ _ _ conv) as [].
    unshelve refine (let c : [Γ |-[bn] A' ≅h B'] := _ in _).
    1: econstructor; tea; boundary.
    exact (typeConvRedBun redA redB c).
  Qed.
  
  (** **** Conversion of types reduced to weak-head normal forms *)
  Inductive ConvTypeRedBunAlg : forall {Γ A B}, ConvTypeRedAlg Γ A B -> Type :=
    | typePiCongBun {Γ A B A' B'}
      (convA : [ Γ |-[bn] A ≅ A'])
      (convB : [ Γ ,, A |-[bn] B ≅ B']) :
      ConvTypeRedBunAlg (typePiCongAlg convA.(bun_conv_ty) convB.(bun_conv_ty))
    | typeUnivConvBun {Γ} :
      ConvTypeRedBunAlg (@typeUnivConvAlg Γ)
    | typeNatConvBun {Γ} :
      ConvTypeRedBunAlg (@typeNatConvAlg Γ)
    | typeEmptyConvBun {Γ} :
      ConvTypeRedBunAlg (@typeEmptyConvAlg Γ) 
    | typeSigCongBun {Γ A B A' B'}
      (convA : [ Γ |-[bn] A ≅ A'])
      (convB : [ Γ ,, A |-[bn] B ≅ B']) :
      ConvTypeRedBunAlg (typeSigCongAlg convA.(bun_conv_ty) convB.(bun_conv_ty))
    | typeListCongBun {Γ A A'}
      (convA : [Γ |-[bn] A ≅ A']) :
      ConvTypeRedBunAlg (typeListCongAlg convA.(bun_conv_ty))
    | typeNeuConvBun {Γ M N T}
      (inf : [ Γ |-[bn] M ~ N ▹ T]) :
      ConvTypeRedBunAlg (typeNeuConvAlg inf.(bun_conv_ne)).

  Lemma bun_conv_ty_red_inv {Γ A B} (conv : [Γ |-[bn] A ≅h B]) :
    ConvTypeRedBunAlg conv.(bun_conv_ty_red).
  Proof.
    destruct conv as [? hA ? hB ? convA].
    destruct convA; cbn; try econstructor; AlgorithmicTypingData.fold_algo.
    + apply prod_ty_inv in hA as [], hB as [].
      unshelve refine (let cA := {| bun_conv_ty := c |} in let cB := {| bun_conv_ty := c0 |} in typePiCongBun cA cB); tea.
      1: boundary. 
      eapply stability1.
      3: now eapply bn_conv_sound in cA.
      all: tea.
    + apply sig_ty_inv in hA as [], hB as [].
      unshelve refine (let cA := {| bun_conv_ty := c |} in let cB := {| bun_conv_ty := c0 |} in typeSigCongBun cA cB); tea.
      1: boundary. 
      eapply stability1.
      3: now eapply bn_conv_sound in cA.
      all: tea.
    + apply list_ty_inv in hA, hB.
      unshelve refine (let cA := {| bun_conv_ty := c |} in typeListCongBun cA); tea.
    + pose proof (fst (snd (snd algo_conv_wh)) _ _ _ _ c) as [whM whN].
      assert [Γ |-[de] M : U].
      1: inversion hA ; subst ; clear hA; solve [inversion whM| assumption].
      assert [Γ |-[de] N : U].
      1: inversion hB ; subst ; clear hB; solve [inversion whN| assumption].
      unshelve refine (let c := {| bun_conv_ne := c |} in typeNeuConvBun c); tea.
      all: now eexists.
  Qed.
    
    
  Inductive ConvNeuBunAlg : forall {Γ T m n}, ConvNeuAlg Γ T m n -> Type :=
    | neuVarConvBun {Γ n decl}
      (hn : in_ctx Γ n decl) :
      ConvNeuBunAlg (neuVarConvAlg hn)
    | neuAppCongBun {Γ m n t u A B}
      (convFun : [ Γ |-[bn] m ~h n ▹ tProd A B ])
      (convArg : [ Γ |-[bn] t ≅ u : A ]) :
      ConvNeuBunAlg (neuAppCongAlg convFun.(bun_conv_ne_red) convArg.(bun_conv_tm))
    | neuNatElimCongBun {Γ n n' P P' hz hz' hs hs'} 
      (convn : [Γ |-[bn] n ~h n' ▹ tNat])
      (convP : [Γ,, tNat |-[bn] P ≅ P'])
      (convhz : [Γ |-[bn] hz ≅ hz' : P[tZero..]])
      (convhs : [Γ |-[bn] hs ≅ hs' : elimSuccHypTy P]) :
      ConvNeuBunAlg (neuNatElimCong convn.(bun_conv_ne_red) convP.(bun_conv_ty) convhz.(bun_conv_tm) convhs.(bun_conv_tm))
    | neuEmptyElimCongBun {Γ P P' e e'} 
      (conve : [Γ |-[bn] e ~h e' ▹ tEmpty])
      (convP : [Γ ,, tEmpty |-[bn] P ≅ P']) :
      ConvNeuBunAlg (neuEmptyElimCong conve.(bun_conv_ne_red) convP.(bun_conv_ty))
    | neuFstCongBun {Γ m n A B} 
      (convm : [ Γ |-[bn] m ~h n ▹ tSig A B ]) :
      ConvNeuBunAlg (neuFstCongAlg convm.(bun_conv_ne_red))
    | neuSndCongBun {Γ m n A B}
      (convm : [ Γ |-[bn] m ~h n ▹ tSig A B ]) :
      ConvNeuBunAlg (neuSndCongAlg convm.(bun_conv_ne_red)).

  Lemma bun_conv_ne_inv {Γ T m n} (conv : [Γ |-[bn] m ~ n ▹ T]) :
    ConvNeuBunAlg (conv.(bun_conv_ne)).
  Proof. 
    destruct conv as [? hm ? hn ? hconv]; cbn; refold.
    destruct hconv; try econstructor; AlgorithmicTypingData.fold_algo.
    + pose proof hm as [? [? [[? [? [-> Htym]]] ?]]%termGen'].
      pose proof hn as [? [? [[? [? [-> Htyn]]] ?]]%termGen'].
      pose proof c as [? hprodm hprodn]%algo_conv_sound; try now econstructor.
      specialize (hprodm _ Htym) as []%prod_ty_inj.
      specialize (hprodn _ Htyn) as []%prod_ty_inj.
      pose proof c as []%algo_conv_wh.
      unshelve refine (
        let convFun : [ Γ |-[bn] m ~h n ▹ tProd A B ] := {| bun_conv_ne_red := c |} in
        let convArg : [ Γ |-[bn] t ≅ u : A ] := {| bun_conv_tm := c0 |} in
        neuAppCongBun convFun convArg); tea.
      3: now boundary.
      all: now econstructor.
    + pose proof hm as [? [? [[->]]]%termGen'].
      pose proof hn as [? [? [[->]]]%termGen'].
      pose proof c as []%algo_conv_wh.
      pose proof c0 as ?%algo_conv_sound; tea.
      unshelve refine (
        let convn : [Γ |-[bn] n ~h n' ▹ tNat] := {| bun_conv_ne_red := c |} in
        let convP : [Γ,, tNat |-[bn] P ≅ P'] := {| bun_conv_ty := c0 |} in
        let convhz : [Γ |-[bn] hz ≅ hz' : P[tZero..]] := {| bun_conv_tm := c1 |} in
        let convhs : [Γ |-[bn] hs ≅ hs' : elimSuccHypTy P] := {| bun_conv_tm := c2 |} in
        neuNatElimCongBun convn convP convhz convhs); tea.
      1,2: now econstructor.
      1: gen_typing.
      1,3: now boundary.
      1,2: econstructor; tea; symmetry.
      1: eapply typing_subst1; gen_typing.
      now eapply elimSuccHypTy_conv.
    + pose proof hm as [? [? [[->]]]%termGen'].
      pose proof hn as [? [? [[->]]]%termGen'].
      pose proof c as []%algo_conv_wh.
      pose proof c0 as ?%algo_conv_sound; tea.
      unshelve refine (
        let conve : [Γ |-[bn] e ~h e' ▹ tEmpty] := {| bun_conv_ne_red := c |} in
        let convP : [Γ ,, tEmpty |-[bn] P ≅ P'] := {| bun_conv_ty := c0 |} in
        neuEmptyElimCongBun conve convP); tea.
      1,2: now econstructor.
      gen_typing.
    + pose proof hm as [? [?[[?[?[->]]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      pose proof c as []%algo_conv_wh.
      unshelve refine (
        let convm : [ Γ |-[bn] m ~h n ▹ tSig A B ] := {| bun_conv_ne_red := c |} in
        neuFstCongBun convm); tea; now econstructor.
    + pose proof hm as [? [?[[?[?[->]]]]]%termGen'].
      pose proof hn as [? [?[[?[?[->]]]]]%termGen'].
      pose proof c as []%algo_conv_wh.
      unshelve refine (
        let convm : [ Γ |-[bn] m ~h n ▹ tSig A B ] := {| bun_conv_ne_red := c |} in
        neuSndCongBun convm); tea; now econstructor.
  Qed.

  Inductive ConvNeuRedBunAlg : forall {Γ T m n}, ConvNeuRedAlg Γ T m n -> Type :=
    | neuConvRedBun {Γ m n A A'} 
      (conv : [Γ |-[bn] m ~ n ▹ A])
      (redA : [A ⇒* A'])
      (whA : whnf A') :
      ConvNeuRedBunAlg (neuConvRed conv.(bun_conv_ne) redA whA).

  Lemma bun_conv_ne_red_inv {Γ T m n} (conv : [Γ |-[bn] m ~h n ▹ T]) :
    ConvNeuRedBunAlg (conv.(bun_conv_ne_red)).
  Proof. 
    destruct conv as [? hm ? hn ? hconv]; cbn.
    dependent inversion hconv; subst; AlgorithmicTypingData.fold_algo.
    now unshelve refine (let conv := {| bun_conv_ne := c |} in neuConvRedBun conv _ _).
  Qed.

  Inductive ConvTermBunAlg : forall {Γ A t u}, ConvTermAlg Γ A t u -> Type :=
    | termConvRedBun {Γ t t' u u' A A'}
      (redA : [A ⇒* A'])
      (redt : [t ⇒* t'])
      (redu : [u ⇒* u' ])
      (conv : [Γ |-[bn] t' ≅h u' : A']) :
      ConvTermBunAlg (termConvRed redA redt redu conv.(bun_conv_tm_red)).

  Lemma bun_conv_tm_inv {Γ A t u} (conv : [Γ |-[bn] t ≅ u : A]) :
    ConvTermBunAlg (conv.(bun_conv_tm)).
  Proof.
    destruct conv as [???? hconv]; cbn.
    dependent inversion hconv; subst.
    pose proof c as []%algo_conv_wh.
    pose proof (r' := r); eapply subject_reduction_type in r' as []; tea.
    unshelve refine (let conv := {| bun_conv_tm_red := c |} in termConvRedBun _ _ _ conv); tea.
    + now boundary.
    + eapply subject_reduction in r0 as []; tea; econstructor; tea; now boundary.
    + eapply subject_reduction in r1 as []; tea; econstructor; tea; now boundary.
  Qed.

  Inductive ConvTermRedBunAlg : forall {Γ A t u}, ConvTermRedAlg Γ A t u -> Type :=
    | termPiCongBun {Γ A B A' B'} 
      (convA : [ Γ |-[bn] A ≅ A' : U])
      (convB : [ Γ ,, A |-[bn] B ≅ B' : U]) :
      ConvTermRedBunAlg (termPiCongAlg convA.(bun_conv_tm) convB.(bun_conv_tm))
    | termNatReflBun {Γ} :
      ConvTermRedBunAlg (@termNatReflAlg Γ)
    | termZeroReflBun {Γ} :
      ConvTermRedBunAlg (@termZeroReflAlg Γ)
    | termSuccCongBun {Γ t t'} 
      (convt : [Γ |-[bn] t ≅ t' : tNat]) :
      ConvTermRedBunAlg (termSuccCongAlg convt.(bun_conv_tm))
    | termEmptyReflBun {Γ} :
      ConvTermRedBunAlg (@termEmptyReflAlg Γ)
    | termFunConvBun {Γ f g A B}
      (whf :whnf f)
      (whg : whnf g)
      (conveta : [ Γ,, A |-[bn] eta_expand f ≅ eta_expand g : B]) :
      ConvTermRedBunAlg (termFunConvAlg whf whg conveta.(bun_conv_tm)) 
    | termSigCongBun {Γ A B A' B'} 
      (convA : [ Γ |-[bn] A ≅ A' : U])
      (convB : [ Γ ,, A |-[bn] B ≅ B' : U]) :
      ConvTermRedBunAlg (termSigCongAlg convA.(bun_conv_tm) convB.(bun_conv_tm))
    | termPairConvBun {Γ p q A B}
      (whp : whnf p)
      (whq : whnf q)
      (convfst : [ Γ |-[bn] tFst p ≅ tFst q : A])
      (convsnd : [ Γ |-[bn] tSnd p ≅ tSnd q : B[(tFst p)..]]) :
      ConvTermRedBunAlg (termPairConvAlg whp whq convfst.(bun_conv_tm) convsnd.(bun_conv_tm))
    | termListCongBun {Γ A A'} 
      (convA : [Γ |-[bn] A ≅ A' : U]) :
      ConvTermRedBunAlg (termListCongAlg convA.(bun_conv_tm))
    | termNilConvBun {Γ A A' AT} :
      ConvTermRedBunAlg (@termNilConvAlg Γ A A' AT)
    | termConsCongBun {Γ A} A' AT {hd hd' tl tl'} 
      (convhd : [Γ |-[bn] hd ≅ hd' : AT])
      (convtl : [Γ |-[bn] tl ≅ tl' : tList AT]) :
      ConvTermRedBunAlg (termConsCongAlg A A' AT convhd.(bun_conv_tm) convtl.(bun_conv_tm))
    | neuMapCompactBun {Γ A B l l'} 
      (r := Map.eta B l) (r' := Map.eta B l')
      (convlst : [Γ |-[bn] r.(Map.lst) ~h r'.(Map.lst) ▹ tList A ])
      (convfn : [Γ |-[bn] r.(Map.fn) ≅ r'.(Map.fn) : arr A B]) :
      ConvTermRedBunAlg (termListNeuConvAlg (neuMapCompact convlst.(bun_conv_ne_red) convfn.(bun_conv_tm)))
    | termNeuConvBun {Γ m n T P} 
      (inf : [Γ |-[bn] m ~ n ▹ T])
      (ispos : isPosType P) :
      ConvTermRedBunAlg (termNeuConvAlg inf.(bun_conv_ne) ispos).

  Lemma bun_conv_tm_red_inv {Γ A t u} (conv : [Γ |-[bn] t ≅h u : A]) :
    ConvTermRedBunAlg (conv.(bun_conv_tm_red)).
  Proof. 
    destruct conv as [? hA ? ht ? hu ? hconv]; cbn.
    destruct hconv; AlgorithmicTypingData.fold_algo.
    - pose proof ht as [? [[->] _]]%termGen'.
      pose proof hu as [? [[->] _]]%termGen'.
      pose proof c as ?%algo_conv_sound; tea.
      unshelve refine (
        let convA : [ Γ |-[bn] A ≅ A' : U] := {| bun_conv_tm := c |} in
        let convB : [ Γ ,, A |-[bn] B ≅ B' : U] := {| bun_conv_tm := c0 |} in
        termPiCongBun convA convB); tea.
      1,2: now boundary.
      eapply stability1; cycle 2; tea; now (econstructor + boundary).
    - econstructor.
    - econstructor.
    - pose proof ht as [? [[->] _]]%termGen'.
      pose proof hu as [? [[->] _]]%termGen'.
      pose proof c as ?%algo_conv_sound; tea.
      unshelve refine (
        let convt : [Γ |-[bn] t ≅ t' : tNat] := {| bun_conv_tm := c |} in
        termSuccCongBun convt); tea.
    - econstructor.
    - eapply prod_ty_inv in hA as [].
      unshelve refine (
      let conveta : [ Γ,, A |-[bn] eta_expand f ≅ eta_expand g : B] := {| bun_conv_tm := c |} in
        termFunConvBun _ _ conveta); tea.
      1: now boundary.
      all: now eapply typing_eta'.
    - pose proof ht as [? [[->] _]]%termGen'.
      pose proof hu as [? [[->] _]]%termGen'.
      pose proof c as ?%algo_conv_sound; tea.
      unshelve refine (
        let convA : [ Γ |-[bn] A ≅ A' : U] := {| bun_conv_tm := c |} in
        let convB : [ Γ ,, A |-[bn] B ≅ B' : U] := {| bun_conv_tm := c0 |} in
        termSigCongBun convA convB); tea.
      1,2: now boundary.
      eapply stability1; cycle 2; tea; now (econstructor + boundary).
    - pose proof c as ?%algo_conv_sound.
      2,3: now econstructor.
      eapply sig_ty_inv in hA as [].
      unshelve refine (
        let convfst : [ Γ |-[bn] tFst p ≅ tFst q : A] := {| bun_conv_tm := c |} in
        let convsnd : [ Γ |-[bn] tSnd p ≅ tSnd q : B[(tFst p)..]] := {| bun_conv_tm := c0 |} in
        termPairConvBun _ _ convfst convsnd); tea.
      1,2: now econstructor.
      2: now econstructor.
      1: eapply typing_subst1; tea; now econstructor.
      econstructor; [now econstructor|].
      eapply typing_subst1; [now symmetry|now econstructor].
    - pose proof ht as [? [[->] _]]%termGen'.
      pose proof hu as [? [[->] _]]%termGen'.
      pose proof c as ?%algo_conv_sound; tea.
      unshelve refine (
        let convA : [Γ |-[bn] A ≅ A' : U] := {| bun_conv_tm := c |} in
        termListCongBun convA); tea.
    - econstructor.
    - eapply list_ty_inv in hA.
      pose proof ht as [? [[->] ?%list_ty_inj]]%termGen'.
      pose proof hu as [? [[->] ?%list_ty_inj]]%termGen'.
      assert [Γ |-[de] A' ≅ A] by (etransitivity; tea; now symmetry).
      pose proof c as ?%algo_conv_sound; tea.
      2: econstructor; tea.
      pose proof c0 as ?%algo_conv_sound; tea.
      2: econstructor; tea; now econstructor.
      unshelve refine (
        let convhd := {| bun_conv_tm := c |} in
        let convtl := {| bun_conv_tm := c0 |} in
        termConsCongBun A' AT convhd convtl); tea.
      * now econstructor.
      * now econstructor.
      * econstructor; tea; now econstructor.
      * econstructor ; tea.
        now econstructor.
      * econstructor ; tea.
        now econstructor.
      * econstructor ; tea.
        now econstructor.
      * now econstructor.   
    - dependent inversion c ; subst ; refold.
      subst r r' r0 r'0 r1 r'1.
      pose proof (map_eta_well_typed ht) as [].
      pose proof (map_eta_well_typed hu) as [].
      set (r := Map.eta A m) in *.
      set (r' := Map.eta A n) in *.
      assert [Γ |-[de] A0 ≅ (Map.srcTy r)].
      {
        eapply algo_conv_sound in c0 as [].
        2-3: now eexists.
        now eapply list_ty_inj, c4.
      }
      assert [Γ |-[de] A0 ≅ (Map.srcTy r')].
      {
        eapply algo_conv_sound in c0 as [].
        2-3: now eexists.
        now eapply list_ty_inj, c5.
      }
      unshelve refine (
        let convlst := {| bun_conv_ne_red := c0 |} in
        let convfn :=  {| bun_conv_tm := c1 |} in
        neuMapCompactBun convlst convfn) ; tea.
      + now eexists.
      + eapply eta_map_lst_whne.
        now eapply algo_conv_wh in c.
      + now eexists. 
      + eapply eta_map_lst_whne.
        now eapply algo_conv_wh in c.
      + clear convlst.
        econstructor.
        all: boundary.
      + clear convlst.
        renToWk.
        eapply typing_wk.
        2: econstructor.
        all: boundary.
      + clear convlst.
        econstructor.
        2: renToWk ; eapply typing_wk.
        1: eapply stability1 ; last first ; tea.
        all: tea.
        3: econstructor.
        all: boundary.
      + clear convlst.
        econstructor.
        2: renToWk ; eapply typing_wk.
        1: eapply stability1 ; last first ; tea.
        all: tea.
        3: econstructor.
        all: boundary.
    - pose proof c as []%algo_conv_wh.
      unshelve refine (
        let inf : [Γ |-[bn] m ~ n ▹ T] := {| bun_conv_ne := c |} in
        termNeuConvBun inf _); tea; now econstructor.
  Qed.

  From Equations Require Import Equations.

  Derive Signature for ConvTypeBunAlg.
  Derive Signature for ConvTypeRedBunAlg.
  Derive Signature for ConvNeuBunAlg.
  Derive Signature for ConvNeuRedBunAlg.
  Derive Signature for ConvTermBunAlg.
  Derive Signature for ConvTermRedBunAlg.
  Derive NoConfusion for term.
  Derive NoConfusion for sort.


Ltac inv_bn H :=
  match type of H with
  | [_ |-[bn] _ ≅ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ty_inv H); depelim h; subst ; clear dependent H
  | [_ |-[bn] _ ≅h _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ty_red_inv H); depelim h; subst ; clear dependent H
  | [_ |-[bn] _ ~ _ ▹ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ne_inv H); depelim h; subst ; clear dependent H
  | [_ |-[bn] _ ~h _ ▹ _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_ne_red_inv H); depelim h; subst ; clear dependent H
  | [_ |-[bn] _ ≅ _ : _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_tm_inv H); depelim h; subst ; clear dependent H
  | [_ |-[bn] _ ≅h _ : _] => 
    let h := fresh "invhyp" in 
    pose proof (h := bun_conv_tm_red_inv H); depelim h;
    try match goal with 
    | Heq : context [H] |- _ => injection Heq; intros 
    end; subst ; clear dependent H
  end.


  (* Lemma bn_inv :
    (forall {Γ A B} (conv : [Γ |-[bn] A ≅ B]), ConvTypeBunAlg conv.(bun_conv_ty))
    × (forall {Γ A B} (conv : [Γ |-[bn] A ≅h B]), ConvTypeRedBunAlg conv.(bun_conv_ty_red))
    × (forall {Γ T m n} (conv : [Γ |-[bn] m ~ n ▹ T]), ConvNeuBunAlg (conv.(bun_conv_ne)))
    × (forall {Γ T m n} (conv : [Γ |-[bn] m ~h n ▹ T]), ConvNeuRedBunAlg (conv.(bun_conv_ne_red)))
    × (forall {Γ A t u} (conv : [Γ |-[bn] t ≅ u : A]), ConvTermBunAlg (conv.(bun_conv_tm)))
    × (forall {Γ A t u} (conv : [Γ |-[bn] t ≅h u : A]), ConvTermRedBunAlg (conv.(bun_conv_tm_red))).
  Proof.
    split; [intros; eapply bun_conv_ty_inv|].
    split; [intros; eapply bun_conv_ty_red_inv|].
    split; [intros; eapply bun_conv_ne_inv|].
    split; [intros; eapply bun_conv_ne_red_inv|].
    split; [intros; eapply bun_conv_tm_inv|].
    intros; eapply bun_conv_tm_red_inv.
  Qed. *)


(** ** Induction principle for bundled algorithmic typing *)

(** This is repeating the same ideas as before, but for typing. *)

Section BundledTyping.

  Context (PTy : context -> term -> Type)
    (PInf PInfRed PCheck : context -> term -> term -> Type).

  #[local] Ltac pre_cond Hyp :=
    lazymatch Hyp with
    | context [PTy ?Γ ?A] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInf ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PInfRed ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> Hyp)
    | context [PCheck ?Γ ?A ?t] =>
        constr:([|-[de] Γ] -> [Γ |-[de] A] -> Hyp)
    end.

  #[local] Ltac post_cond Hyp :=
    lazymatch Hyp with
    | context C [PTy ?Γ ?A] =>
        context C [PTy Γ A × [Γ |-[de] A]]
    | context C [PInf ?Γ ?A ?t] =>
        context C [PInf Γ A t × [Γ |-[de] t : A]]
    | context C [PInfRed ?Γ ?A ?t] =>
        context C [PInfRed Γ A t × [Γ |-[de] t : A]]
    | context C [PCheck ?Γ ?A ?t] =>
        context C [PCheck Γ A t × [Γ |-[de] t : A]]
    | ?Hyp' => Hyp'
    end.

  #[local] Ltac bundle Hyp :=
    lazymatch Hyp with
      | [?Γ |-[al] ?A] => constr:([Γ |-[bn] A])
      | [?Γ |-[al] ?t ▹ ?A] => constr:([Γ |-[bn] t ▹ A])
      | [?Γ |-[al] ?t ▹h ?A] => constr:([Γ |-[bn] t ▹h A])
      | [?Γ |-[al] ?t ◃ ?A] => constr:([Γ |-[bn] t ◃ A])
      | ?Hyp' => constr:(Hyp')
    end.

  #[local] Ltac strong_step step :=
    lazymatch step with
      | ?Hyp -> ?T => let Hyp' := (post_cond Hyp) with T' := (strong_step T) in constr:(Hyp' -> T')
      | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := strong_step T' in exact T''))
      | ?T => (pre_cond T)
    end.

  #[local] Ltac weak_concl concl :=
    lazymatch concl with
    | ?Hyp -> ?T => let T' := weak_concl T in let Hyp' := bundle Hyp in constr:(Hyp' -> T')
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
      let T' := ltac:(eval hnf in (T x)) in let T'' := weak_concl T' in exact T''))
    | ?T => constr:(T)
    end.

  #[local] Ltac strong_concl concl :=
  lazymatch concl with
  | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := strong_concl T' in exact T''))
  | ?T => let T' := (post_cond T) in let T'' := (pre_cond T') in constr:(T'')
  end.

  #[local] Ltac strong_statement T :=
    lazymatch T with
      | ?Step -> ?T => let Step' := strong_step Step in let T' := strong_statement T in constr:(Step' -> T')
      | ?Chd × ?Ctl => let Chd' := strong_concl Chd in let Ctl' := strong_statement Ctl in constr:(Chd' × Ctl')
      | ?Cend => let Cend' := strong_concl Cend in constr:(Cend')
    end.

  #[local] Ltac weak_statement T :=
  lazymatch T with
    | ?Step -> ?T => let Step' := strong_step Step in let T' := weak_statement T in constr:(Step' -> T')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Chd × ?Ctl => let Chd' := weak_concl Chd in let Ctl' := weak_statement Ctl in constr:(Chd' × Ctl')
    | ?Cend => let Cend' := weak_concl Cend in constr:(Cend')
  end.

  Let PTy' (c : context) (t : term) :=
        [ |-[ de ] c] -> PTy c t × [c |-[ de ] t].
  Let PInf' (c : context) (t t1 : term) :=
     [ |-[ de ] c] -> PInf c t t1 × [c |-[ de ] t1 : t].
  Let PInfRed' (c : context) (t t1 : term) :=
       [ |-[ de ] c] -> PInfRed c t t1 × [c |-[ de ] t1 : t].
  Let PCheck' (c : context) (t t1 : term) :=
         [ |-[ de ] c] ->
         [c |-[ de ] t] -> PCheck c t t1 × [c |-[ de ] t1 : t].

  (** The main theorem *)
  Theorem algo_typing_discipline : ltac:(
    let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
    let ind := strong_statement t in
    exact ind).
  Proof.
    intros.
    subst PTy' PInf' PInfRed' PCheck'.
    apply AlgoTypingInduction.
    1-10: solve [intros ;
      repeat unshelve (
        match reverse goal with
          | IH : context [prod] |- _ => destruct IH ; [..|shelve] ; gen_typing
        end) ;
      now split ; [|econstructor] ; eauto].
    - intros * ? IHI ? IHC ?.
      destruct IHI as [? IHt].
      1: gen_typing.
      destruct IHC ; tea.
      1: now eapply boundary, prod_ty_inv in IHt as [].
      split ; [|econstructor] ; eauto.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHn ? IHP ? IHz ? IHs ?.
      assert [|-[de] Γ,, tNat]
        by (econstructor ; tea ; now econstructor).
      assert [Γ |-[ de ] P[tZero..]].
      {
        eapply typing_subst1.
        1: now econstructor.
        now eapply IHP.
      }
      assert [Γ |-[de] elimSuccHypTy P]
        by now eapply elimSuccHypTy_ty.
      split ; [eauto 10 |..].
      econstructor.
      + now eapply IHP.
      + now eapply IHz.
      + now eapply IHs.
      + now eapply IHn.
    - intros.
      split ; [eauto|..].
      now econstructor.
    - intros * ? IHe ? IHP ?.
      assert [|-[de] Γ,, tEmpty]
        by (econstructor ; tea ; now econstructor).
      split ; [eauto|..].
      econstructor.
      + now eapply IHP.
      + now eapply IHe.
    - intros * ? ihA ? ihB ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      split; [eauto|now econstructor].
    - intros * ? ihA ? ihB ? iha ? ihb ?.
      edestruct ihA as []; tea.
      edestruct ihB as [].
      1: gen_typing.
      edestruct iha as []; tea.
      edestruct ihb as []; tea.
      1: now eapply typing_subst1.
      split;[eauto|now econstructor].
      (* why is that not found by eauto ? *)
      eapply X17; tea; now split.
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ih ?.
      edestruct ih as []; tea.
      split;[eauto|now econstructor].
    - intros * ? ihA ? ihhd ? ihtl ?.
      edestruct ihA as []; tea.    
      edestruct ihhd as []; tea.    
      edestruct ihtl as []; tea;[now econstructor|].
      split; [eauto|now econstructor].    
    - intros * ? ihA ? ihB ? ihf ? ihl ?.
      edestruct ihA as []; tea.
      edestruct ihB as []; tea.
      edestruct ihf as []; tea; [now eapply wft_simple_arr|].
      edestruct ihl as []; tea; [now econstructor|].
      split; [|now econstructor]. 
      (* why does it not work ?? *)
      eapply X23; tea; split; tea.   
    - intros * ? IH HA ?.
      destruct IH as [? IH] ; tea.
      split ; [eauto|..].
      econstructor ; tea.
      eapply subject_reduction_type, RedConvTyC in HA.
      1: eassumption.
      now boundary.
    - intros * ? IHt HA ?.
      destruct IHt as [? IHt] ; eauto.
      split ; [eauto|].
      econstructor ; tea.
      eapply algo_conv_sound in HA ; tea.
      now boundary.
  Qed.

  Definition BundledTypingInductionConcl : Type :=
    ltac:(let t := eval red in (AlgoTypingInductionConcl PTy PInf PInfRed PCheck) in
      let t' := weak_statement t in exact t').

  Corollary BundledTypingInduction :
    ltac:(
      let t := (type of (AlgoTypingInduction PTy PInf PInfRed PCheck)) in
      let ind := weak_statement t in
      exact ind).
  Proof.
    intros.
    repeat match goal with |- prod _ _ => split end.
    all: intros * [].
    all: apply algo_typing_discipline ; assumption.
  Qed.

End BundledTyping.

Section TypingSoundness.

  Let PTy (Γ : context) (A : term) :=
    [|-[de] Γ] -> [Γ |-[de] A].
  Let PInf (Γ : context) (A t : term) :=
    [|-[de] Γ] ->
    [Γ |-[de] t : A].
  Let PCheck (Γ : context) (A t : term) :=
    [Γ |-[de] A] ->
    [Γ |-[de] t : A].

  Theorem algo_typing_sound : AlgoTypingInductionConcl PTy PInf PInf PCheck.
  Proof.
    subst PTy PInf PCheck.
    red.
    pose proof (algo_typing_discipline 
      (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)) as [H' H] 
      ;
    cycle -1.
    1: repeat (split ; [
      intros ; apply H' ; tea ; match goal with H : sigT _ |- _ => destruct H | _ => idtac end ; gen_typing 
      | ..] ; clear H' ; try destruct H as [H' H]).
    1: now intros ; apply H ; gen_typing.
    all: now constructor.
  Qed.

End TypingSoundness.

Theorem bn_alg_typing_sound :
BundledTypingInductionConcl
  (fun Γ A => [Γ |-[de] A])
  (fun Γ A t => [Γ |-[de] t : A])
  (fun Γ A t => [Γ |-[de] t : A])
  (fun Γ A t => [Γ |-[de] t : A]).
Proof.
  red.
  prod_splitter.
  all: intros * [].
  all: match goal with H : context [al] |- _ => eapply algo_typing_sound in H end.
  all: prod_hyp_splitter.
  all: now eassumption.
Qed.

Lemma bn_typing_sound Γ t A :
  [Γ |-[bn] t : A] -> [Γ |-[de] t : A].
Proof.
  intros [???Hty?].
  econstructor ; tea.
  now eapply algo_typing_sound in Hty.
Qed.

Corollary inf_conv_decl Γ t A A' :
[Γ |-[al] t ▹ A] ->
[Γ |-[de] A ≅ A'] ->
[Γ |-[de] t : A'].
Proof.
  intros Ht Hconv.
  apply algo_typing_sound in Ht.
  2: boundary.
  now econstructor.
Qed.