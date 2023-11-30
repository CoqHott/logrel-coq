
From Coq Require Import ssreflect.
From Equations Require Import Equations.
From smpl Require Import Smpl.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import DirectedDirections DirectedContext DirectedDirectioning DirectedMorphisms DirectedDeclarativeTyping.
From LogRel Require Import Utils BasicAst Notations GenericTyping.

(* TODO: reorganize files! *)
Section DirectedValid.

  Context `{GenericTypingProperties}.
  Context {Δ} (wfΔ: [ |- Δ ]).

  Let Pctx (θ: context) := (* [ |-( ) θ ] -> *) unit (* TODO *).

  Let Pty Θ d A := (* forall (wfA : [ Θ |-( d ) A ]), *)
    forall (σ τ: nat -> term) ϕ,
      [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      let '(d', act) := compute_dir_and_action (dirs Θ) A σ τ ϕ in
      dir_leq d' d ×
      match d with
      | Fun => [ Δ |- act : arr A[σ] A[τ] ]
      | Cofun => [ Δ |- act : arr A[τ] A[σ] ]
      | Discr => [ Δ |- A[σ] ≅ A[τ] ]
      end.

  Let Ptm Θ dt A dA t := (* forall (wtt: [ Θ |-( dt ) t : A @( dA ) ]), *)
    forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] ->
    (let '(v,w,A) :=
      dispatchDir (dirs Θ) σ τ ϕ A dA t[σ] t[τ] in
     let '(d', act) := (compute_dir_and_action (dirs Θ) t σ τ ϕ) in
    dir_leq d' dt × termRelPred Δ v w dt A act).

  Let Pconvty Θ d A B := (* [ Θ |-( d ) A ≅ B ] -> *)
    forall (σ τ: nat -> term) ϕ,
      [ Δ |- ϕ : σ -( )- τ : Θ ] ->
      let '(dA, actA) := compute_dir_and_action (dirs Θ) A σ τ ϕ in
      let '(dB, actB) := compute_dir_and_action (dirs Θ) B σ τ ϕ in
      dir_leq dA d ×
      dir_leq dB d ×
      match d with
      | Fun => [ Δ |- actA ≅ actB : arr A[σ] A[τ] ]
      | Cofun => [ Δ |- actA ≅ actB : arr A[τ] A[σ] ]
      | Discr => unit
      end.

  Let Pconvtm Θ d A dA t u := (* [ Θ |-( dt ) t ≅ u : A @( dA ) ] -> *)
    forall (σ τ: nat -> term) ϕ, [ Δ |- ϕ : σ -( )- τ : Θ ] ->
    (let '(v,w,A) :=
      dispatchDir (dirs Θ) σ τ ϕ A dA t[σ] t[τ]
      (* need only one dispatch? the other should be convertible? *)
      (* will need a lemma saying if compute_action is well typed,
         then dispatch dir gives convertible components *)
    in
      let '(dt, actt) := compute_dir_and_action (dirs Θ) t σ τ ϕ in
      let '(du, actu) := compute_dir_and_action (dirs Θ) u σ τ ϕ in
      dir_leq dt d ×
      dir_leq du d ×
    match d with
    | Fun => [ Δ |- actt ≅ actu : termRelArr Δ v w A ]
    | Cofun => [ Δ |- actt ≅ actu : termRelArr Δ w v A ]
    | Discr => unit
    end).


  Definition DirectedAction :
    DirectedDeclarativeTyping.WfDeclInductionConcl Pctx Pty Ptm Pconvty Pconvtm.
  Proof.
    eapply DirectedDeclarativeTyping.WfDeclInduction.
    all: subst Pctx Pty Ptm Pconvty Pconvtm.
    - exact tt. (* TODO: what do i need exactly for contexts? *)
    - intros; exact tt.
    - intros; exact tt.
    - intros; exact tt.
    - (* wfTypeU *)
      intros Θ d wfΘ _ σ τ l rel.
      split. 1: now constructor.
      (* TODO: for reflexivity, look at generic consequences or something, there is a type class for this *)
      (* WAIT in this case its not needed, you have it for every constructors *)
      destruct d.
      1-3: admit.
    - (* wfTypeProd *)
      intros Θ A dA B dB d wfA IHA wfB IHB maxd σ τ ϕ rel.
      cbn -[subst_term].
      have IHA_ := IHA σ τ ϕ _.
      remember (compute_dir_and_action (dirs Θ) A σ τ ϕ) as dir_act_A.
      destruct dir_act_A as [[] actA]; cycle 2.
      + have IHB_ := IHB (tRel 0 .: σ) (tRel 0 .: τ) (cons err_term ϕ) _.
        remember (compute_dir_and_action _ B _ _ _) as dir_act_B.
        destruct dir_act_B as [[] actB]; cycle 2.
        { split. 1: now constructor.
          cbv in maxd.
          destruct dA, dB; inversion maxd; cbn in *.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.
          - unfold up_term_term.
            admit.
        }
        { admit. }
        { admit. }
      + admit.
      + admit.
        (* constructor. *)
(*         * eapply typing_subst; tea. *)
(*           now eapply typing_erased. *)
(*           admit. *)
(*         * now trivial. *)
(*         * admit. *)
    - (* wfTypeUniv *)
      admit.
(*       intros Θ d A wtA IHA wfA σ τ l rel. *)
(*       pose (X := IHA wtA _ _ l rel). *)
(*       admit. *)
(*       (* destruct d. *) *)
(*       (* + inversion X. *) *)
(*       (*   eexists. eassumption. *) *)
(*       (* + inversion X. *) *)
(*       (*   eexists. eassumption. *) *)
(*       (* + inversion X. eapply convUniv. *) *)
(*       (*   exact H. *) *)
    - (* wfVar *)
      intros Θ d' n d A dA wfΘ IHΘ inctx dleq σ τ ϕ rel.
      (* maybe will need something on the context in the induction *)
      admit.
(*       admit. *)
    - (* wfTermProd *)
      admit.
(*       intros Θ d A B wfA IHA wfB IHB wfProd σ τ rel. *)
(*       destruct d. *)
(*       + admit. *)
(*       + admit. *)
(*       + admit. *)
    - (* wfTermLam *)
      admit.
(*       intros Θ dt dT A B t wfA IHA wfB IHB wtLam σ τ rel. *)
(*       destruct dT; simpl in *. *)
(*       + admit. *)
(*       + admit. *)
(*       + destruct dt. *)
(*         * constructor. *)
(*           { *)
(*             eapply typing_subst; tea. *)
(*             now eapply typing_erased. *)
(*             now eapply TermRel_WellSubst_l. *)
(*           } *)
(*           { admit. } *)
(*         * admit. *)
(*         * constructor. *)
(*           admit. *)
    - (* wfTermApp *)
      admit.
(*       intros Θ d dA f a A B wtf IHf wta IHa wtApp σ τ rel. *)
(*       destruct dA. *)
(*       + cbn in *. admit. *)
(*       + admit. *)
(*       + cbn in *. admit. *)
    - (* wfTermConv *)
      admit.
  Abort.

End DirectedValid.
