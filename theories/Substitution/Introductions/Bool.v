From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations LContexts Context NormalForms Weakening GenericTyping Monad LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Induction Irrelevance Escape Reflexivity Weakening Monotonicity Split Neutral Transitivity Reduction Application Universe SimpleArr.
From LogRel.Substitution Require Import Irrelevance Properties Conversion SingleSubst Reflexivity Monotonicity.
From LogRel.Substitution.Introductions Require Import Universe Pi SimpleArr Var Nat.

Set Universe Polymorphism.

Section Bool.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma boolRed {wl Γ l} : [|- Γ]< wl > -> [Γ ||-<l> tBool]< wl >.
Proof. 
  intros; eapply LRBool_; constructor; eapply redtywf_refl; gen_typing.
Defined.

Lemma WboolRed {wl Γ l} : [|- Γ]< wl > -> W[Γ ||-<l> tBool]< wl >.
Proof.
  intros ; now eapply LogtoW, boolRed.
Defined.

Lemma boolValid {wl Γ l} (VΓ : [||-v Γ]< wl >) : [Γ ||-v<l> tBool | VΓ]< wl >.
Proof.
  unshelve econstructor; intros.
  + now eapply WboolRed.
  + cbn ; eapply EqLogtoW.
    constructor; eapply redtywf_refl.
    now gen_typing.
Defined.

Lemma boolconvValid {wl Γ l} (VΓ : [||-v Γ]< wl >) (VBool : [Γ ||-v<l> tBool | VΓ]< wl >) : 
  [Γ ||-v<l> tBool ≅ tBool | VΓ | VBool]< wl >.
Proof.
  constructor; intros ; cbn.
  unshelve eapply EqLogtoW' ; [exact (boolRed wfΔ) | ].
  constructor; cbn; eapply redtywf_refl; gen_typing.
Qed.

Lemma boolTermRed {wl Δ} (wfΔ : [|-Δ]< wl >) : [Δ ||-<one> tBool : U | LRU_ (redUOne wfΔ)]< wl >.
Proof.
  econstructor.
  + eapply redtmwf_refl; gen_typing.
  + constructor.
  + gen_typing.
  + now eapply (boolRed (l:= zero)).
Defined.

Lemma boolTermValid {wl Γ} (VΓ : [||-v Γ]< wl >):  [Γ ||-v<one> tBool : U | VΓ | UValid VΓ]< wl >.
Proof.
  constructor; intros.
  - eapply TmLogtoW' ; eapply boolTermRed.
    Unshelve. assumption.
  - unshelve eapply TmEqLogtoW'.
    1: cbn ; eapply LRU_ ; unshelve econstructor ; [ | now econstructor | eassumption |.. ].
    1: eapply redtywf_refl ; gen_typing.
    eexists (boolTermRed wfΔ) (boolTermRed wfΔ) (boolRed wfΔ); cbn.
    + gen_typing.
    + now eapply (boolRed (l:=zero)).
    + constructor; eapply redtywf_refl; gen_typing.
Qed.

Lemma trueRed {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tTrue : _ | LRBool_ l NN]< wl >.
Proof.
  exists tTrue.
  1,2: gen_typing.
  constructor.
Defined.

Lemma WtrueRed {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): W[Γ ||-<l> tTrue : _ | LogtoW (LRBool_ l NN)]< wl >.
Proof.
  exists (leaf _).
  intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tTrue.
  + eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma falseRed {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tFalse : _ | LRBool_ l NN]< wl >.
Proof.
  exists tFalse.
  1,2: gen_typing.
  constructor.
Defined.


Lemma WfalseRed {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): W[Γ ||-<l> tFalse : _ | LogtoW (LRBool_ l NN)]< wl >.
Proof.
  exists (leaf _).
  intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tFalse.
  + eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma trueRedEq {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tTrue ≅ tTrue : _ | LRBool_ l NN]< wl >.
Proof.
  exists tTrue tTrue.
  1-3: gen_typing.
  constructor.
Defined.

Lemma WtrueRedEq {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >):
  W[Γ ||-<l> tTrue ≅ tTrue : _ | LogtoW (LRBool_ l NN)]< wl >.
Proof.
  exists (leaf _) ; intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tTrue tTrue.
  1,2: eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma trueValid {wl Γ l} (VΓ : [||-v Γ]< wl >): 
  [Γ ||-v<l> tTrue : tBool | VΓ | boolValid VΓ]< wl >.
Proof.
  constructor; intros ; cbn.
  + eapply TmLogtoW, trueRed ; assumption.
  + eapply TmEqLogtoW, trueRedEq; tea.
Qed.

Lemma falseRedEq {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >): [Γ ||-<l> tFalse ≅ tFalse : _ | LRBool_ l NN]< wl >.
Proof.
  exists tFalse tFalse.
  1-3: gen_typing.
  constructor.
Defined.

Lemma WfalseRedEq {wl Γ l} {NN : [Γ ||-Bool tBool]< wl >} (wfΓ : [|- Γ]< wl >):
  W[Γ ||-<l> tFalse ≅ tFalse : _ | LogtoW (LRBool_ l NN)]< wl >.
Proof.
  exists (leaf _) ; intros wl' Ho Ho' ; pose (f := over_tree_le Ho).
  exists tFalse tFalse.
  1,2: eapply redtmwf_Ltrans ; [eassumption | now gen_typing].
  + eapply convtm_Ltrans ; [eassumption | now gen_typing].
  + constructor.
Defined.

Lemma falseValid {wl Γ l} (VΓ : [||-v Γ]< wl >): 
  [Γ ||-v<l> tFalse : tBool | VΓ | boolValid VΓ]< wl >.
Proof.
  constructor; intros ; cbn.
  + eapply TmLogtoW, falseRed ; assumption.
  + eapply TmEqLogtoW, falseRedEq; tea.
Qed.

Fixpoint alphaRed_auxnat {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  (t0 : term) (n : [Γ ||-Nat t0 : tNat | NNN ]< wl >) {struct n} : term :=
  match n with
  | Build_NatRedTm nf0 _ _ prop0 => alphaRed_auxnat' nf0 prop0
  end
with alphaRed_auxnat' {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
       (t0 : term) (n : NatProp NNN t0) {struct n} : term :=
       match n with
       | NatRedTm.zeroR => tZero
       | @NatRedTm.succR _ _ _ _ _ _ _ _ _ _ _ n0 n1 => tSucc (alphaRed_auxnat n0 n1)
       | @NatRedTm.neR _ _ _ _ _ _ _ _ _ _ _ ne _ => ne
       end.

Lemma ty_nSucc wl Γ k n :
  [Γ |-[ ta ] n : tNat]< wl > ->
  [Γ |-[ ta ] (nSucc k n) : tNat]< wl > .
Proof.
  revert n ; induction k ; intros n Hn ; [now auto | ].
  cbn ; eapply ty_succ.
  now eapply IHk.
Qed.

Lemma convtm_nSucc wl Γ k n n' :
  [Γ |-[ ta ] n ≅ n' : tNat ]< wl > ->
  [Γ |-[ ta ] nSucc k n ≅ nSucc k n' : tNat ]< wl >.
Proof.
  induction k ; intros Hn ; [now auto | ].
  cbn ; eapply convtm_succ.
  now eapply IHk.
Qed.
  
Lemma nSucc_Red {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n (Hn: [Γ ||-Nat n : tNat | NNN ]< wl >) :
  forall k,
    [Γ ||-Nat nSucc k n : tNat | NNN ]< wl >
with nSucc_NatProp {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
       n (Hn: NatProp NNN n) :
  forall k,
    NatProp NNN (nSucc k n).
Proof.
  - induction k ; cbn ; [now auto | ].
    econstructor.
    + eapply redtmwf_refl, ty_succ, ty_nSucc.
      destruct Hn, red.
      now eapply redtm_ty_src.
    + eapply convtm_succ, convtm_nSucc.
      destruct Hn, red.
      eapply convtm_exp ; try eassumption ; now gen_typing.
    + now econstructor.
  - induction k ; cbn ; [now auto | ].
    econstructor.
    econstructor ; [ | | eassumption].
    + eapply redtmwf_refl, ty_nSucc.
      destruct Hn.
      * destruct NNN, red ; cbn in *.
        gen_typing.
      * destruct n0, red ; cbn in *.
        gen_typing.
      * now destruct r.
    + eapply convtm_nSucc.
      destruct Hn.
      * destruct NNN, red ; cbn in * ; gen_typing.
      * destruct n0, red ;  cbn in *.
        eapply convtm_succ, convtm_exp ; try eassumption ; now gen_typing.
      * destruct r.
        eapply convtm_convneu ; [ | assumption].
        now constructor.
Qed.

Lemma WnSucc_Red {wl Γ l n NNN} :
  forall k,
    W[ Γ ||-< l > n : tNat | LogtoW (LRNat_ _ NNN) ]< wl > ->
    W[ Γ ||-< l > nSucc k n : tNat | LogtoW (LRNat_ _ NNN) ]< wl > .
Proof.
  intros k [d Hd] ; exists d.
  intros wl' Ho Ho' ; cbn.
  now eapply nSucc_Red, Hd.
Qed.  

Fixpoint alphaRed_auxnatred {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n (Hn: [Γ ||-Nat n : tNat | NNN ]< wl >) {struct Hn} :
  forall k,
    [Γ |-[ ta ] tAlpha (nSucc k n) :⤳*: tAlpha (nSucc k (alphaRed_auxnat n Hn)) : tNat ]< wl >
with alphaRed_auxnatred' {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
       n (Hn: NatProp NNN n) {struct Hn}:
  forall k,
  [Γ |-[ ta ] tAlpha (nSucc k n) :⤳*: tAlpha (nSucc k (alphaRed_auxnat' n Hn)) : tNat ]< wl >.
Proof.
  - destruct Hn ; cbn ; intros k.
    etransitivity.
    2: unshelve eapply (alphaRed_auxnatred' wl _ NNN nf prop).
    unshelve econstructor ; [now gen_typing | ].
    destruct red. now eapply redtm_alphaSubst.
    Unshelve.
    2: eassumption.
  - pose proof (help := LRNat_ one NNN) ; escape.
    destruct Hn ; cbn ; intros k.
    + eapply redtmwf_refl, ty_alpha.
      induction k ; cbn ; now gen_typing.
    + replace (nSucc k (tSucc n)) with (nSucc (S k) n) by (induction k; [reflexivity | cbn ; now f_equal ]).
      replace (nSucc k (tSucc (alphaRed_auxnat n n0)))
        with (nSucc (S k)(alphaRed_auxnat n n0)) by (induction k; [reflexivity | cbn ; now f_equal ]).
      now eapply alphaRed_auxnatred.
    + eapply redtmwf_refl,ty_alpha.
      induction k ; cbn ; [ | now gen_typing].
      now destruct r.
Qed.

Fixpoint alphaRed_aux {wl l Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n (Hn: [Γ ||-Nat n : tNat | NNN ]< wl >) {struct Hn} :
  forall k,
    W[Γ ||-<l> tAlpha (nSucc k (alphaRed_auxnat n Hn)) : _ | LogtoW (LRNat_ l NNN) ]< wl >
with alphaRed_aux' {wl l Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n (Hn: NatProp NNN n) {struct Hn}:
  forall k,
    W[Γ ||-<l> tAlpha (nSucc k (alphaRed_auxnat' n Hn)) : _ | LogtoW (LRNat_ l NNN) ]< wl >.
Proof.
  - destruct Hn ; cbn.
    now eapply alphaRed_aux'.
  - pose (help := LRNat_ l NNN) ; escape.
    destruct Hn ; cbn ; intros k.
    + change (nSucc k tZero) with (nat_to_term k).
      destruct (decidInLCon wl k) as [ | notin].
      1: unshelve econstructor ; [constructor 1 | intros wl' Ho Ho'].
      * exists (nat_to_term m).
        3: unfold nat_to_term ; eapply nSucc_NatProp ; now constructor.
        -- cbn in *.
           eapply redtmwf_Ltrans ; [exact Ho' | ].
           econstructor.
           1: unfold nat_to_term ; eapply ty_nSucc ; now gen_typing.
           eapply redtm_alpha ; eauto ; now gen_typing.
        -- unfold nat_to_term ; eapply convtm_nSucc.
           eapply convtm_Ltrans ; [exact Ho' | ] ; now gen_typing.
      * exists (ϝnode _ (ne := notin) (fun m => leaf _)).
        intros wl' Ho Ho' ; cbn in *.
        destruct (decidInLCon wl' k) as [m i | ne] ; [.. | now inversion Ho'].
        pose (f := @LCon_le_step  _ _ _ m notin (wfLCon_le_id _)).
        exists (nat_to_term m).
        3: unfold nat_to_term ; eapply nSucc_NatProp ; now constructor.
        -- cbn in *.
           eapply redtmwf_Ltrans ; [exact Ho' | ].
           econstructor ; [eapply ty_Ltrans ; try eassumption | ].
           1: unfold nat_to_term ; eapply ty_nSucc ; now gen_typing.
           eapply redtm_alpha ; eauto ; [ | now constructor].
           eapply wfc_Ltrans ; try eassumption.
           now gen_typing.
        -- unfold nat_to_term ; eapply convtm_nSucc.
           eapply convtm_Ltrans ; [exact Ho | ] ; now gen_typing.
    + replace (nSucc k (tSucc (alphaRed_auxnat n n0))) with (nSucc (S k) (alphaRed_auxnat n n0))
        by (induction k; [reflexivity | cbn ; now f_equal ]).
      now eapply alphaRed_aux.
    + exists (leaf _) ; intros wl' Ho Ho'.
      irrelevanceRefl ; unshelve eapply (Tm_Ltrans Ho') ; [eassumption | ].
      econstructor ; [eapply redtmwf_refl | | econstructor 3 ; econstructor] ; destruct r.
      1,3: eapply ty_alpha ; induction k ; cbn ; now gen_typing.
      1: eapply convtm_convneu ; [now constructor | ].
      all: now eapply convneu_alpha.
Qed.      
  
Lemma alphaRed {wl Γ l n} {NNN : [Γ ||-Nat tNat]< wl >} :
  [Γ ||-<l> n : _ | LRNat_ l NNN]< wl > ->
  W[Γ ||-<l> tAlpha n : _ | LogtoW (LRNat_ l NNN)]< wl >.
Proof.
  intros Hn.
  pose (Help1 := alphaRed_auxnatred _ Hn 0).
  pose (Help2 := alphaRed_aux (l := l) _ Hn 0) ; cbn in *.
  eapply WredwfSubstTerm.
  all: eassumption.
Qed.

Lemma WalphaRed {wl Γ l n} {NNN : [Γ ||-Nat tNat]< wl >} :
  W[Γ ||-<l> n : _ | LogtoW (LRNat_ l NNN)]< wl > ->
  W[Γ ||-<l> tAlpha n : _ | LogtoW (LRNat_ l NNN)]< wl >.
Proof.
  intros [d Hd].
  eapply (TreeTmSplit d); intros wl' Ho HN.
  Wirrelevance0 ; [reflexivity | now eapply alphaRed, Hd].
  Unshelve.
  cbn ; now eapply over_tree_le.
Qed.

Lemma NatProp_tZero_inv {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  (Hn : NatProp NNN tZero) :
  Hn = NatRedTm.zeroR.
Proof.
 refine (match Hn as Hn0 in NatProp _ x  with
              | NatRedTm.zeroR => _
              | NatRedTm.succR me => _
              | NatRedTm.neR me => _
         end).
 + reflexivity.
 + intros A x ; exact x.
 + destruct t ; cbn in *.
   all: try now (intros A x ; exact x).
   destruct me ; cbn in *.
   epose proof (Heq := convneu_whne refl).
   inversion Heq.
Qed.

Lemma NatProp_tSucc_inv {wl Γ} {NNN : [Γ ||-Nat tNat]< wl >} n
  (Hn : NatProp NNN (tSucc n)) :
  ∑ Hm, Hn = NatRedTm.succR Hm.
Proof.
  refine (match Hn as Hn0 in NatProp _ x  with
              | NatRedTm.zeroR => _
              | NatRedTm.succR me => _
              | NatRedTm.neR me => _
         end).
  + intros A x ; exact x.
  + exists me ; reflexivity.
  + destruct t ; try (now intros A x).
    destruct me.
    epose proof (Heq := convneu_whne refl).
    inversion Heq.
Qed.
   
Fixpoint alphaRedEq_aux {wl l Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n n' (Hn: [Γ ||-Nat n : tNat | NNN ]< wl >)
  (Hn': [Γ ||-Nat n' : tNat | NNN ]< wl >)
  (Hneq: [Γ ||-Nat n ≅ n' : tNat | NNN ]< wl >)
  {struct Hneq} :
  forall k,
    W[Γ ||-<l> tAlpha (nSucc k (alphaRed_auxnat n Hn)) ≅
                 tAlpha (nSucc k (alphaRed_auxnat n' Hn')): _ | LogtoW (LRNat_ l NNN) ]< wl >
with alphaRedEq_aux' {wl l Γ} {NNN : [Γ ||-Nat tNat]< wl >}
  n n' (Hn: NatProp NNN n)
  (Hn': NatProp NNN n')
  (Hneq: NatPropEq NNN n n') {struct Hneq}:
  forall k,
    W[Γ ||-<l> tAlpha (nSucc k (alphaRed_auxnat' n Hn)) ≅
                 tAlpha (nSucc k (alphaRed_auxnat' n' Hn')) : _ | LogtoW (LRNat_ l NNN) ]< wl >.
Proof.
  - destruct Hneq, Hn, Hn' ; intros k.
    epose proof (Heq := redtmwf_det (NatProp_whnf prop0) (fst (NatPropEq_whnf prop)) red redL).
    epose proof (Heq' := redtmwf_det (NatProp_whnf prop1) (snd (NatPropEq_whnf prop)) red0 redR).
    subst ; cbn in *.
    now unshelve eapply alphaRedEq_aux'.
  - destruct Hneq ; intros k ; cbn in *.
    + epose proof (Heq := NatProp_tZero_inv Hn). 
      epose proof (Heq' := NatProp_tZero_inv Hn').
      subst.
      now eapply WreflLRTmEq, alphaRed_aux'.
    + destruct (NatProp_tSucc_inv _ Hn) as [Hm Heq].
      destruct (NatProp_tSucc_inv _ Hn') as [Hm' Heq'].
      subst ; cbn in *.
      replace (nSucc k (tSucc (alphaRed_auxnat n Hm))) with
        (nSucc (S k) (alphaRed_auxnat n Hm)) by (induction k ; [reflexivity | cbn ; now f_equal]).
      replace (nSucc k (tSucc (alphaRed_auxnat n' Hm'))) with
        (nSucc (S k) (alphaRed_auxnat n' Hm')) by (induction k ; [reflexivity | cbn ; now f_equal]).
      now eapply alphaRedEq_aux.
    + destruct r, Hn.
      1,2: eapply convneu_whne in conv ; now inversion conv.
      destruct Hn'.
      1,2: symmetry in conv.
      1,2: eapply convneu_whne in conv ; now inversion conv.
      pose (help := LRNat_ l NNN) ; escape ; cbn.
      eapply Wreflect.
      1: now eapply Wcompleteness.
      1,2: eapply ty_alpha.
      1,2: destruct r, r0 ; induction k ; cbn ; now gen_typing.
      now eapply convneu_alpha.
Qed.

Lemma alphaRedEq {wl Γ l n n'} {NNN : [Γ ||-Nat tNat]< wl >} :
  [Γ ||-<l> n : _ | LRNat_ l NNN]< wl > ->
  [Γ ||-<l> n' : _ | LRNat_ l NNN]< wl > ->
  [Γ ||-<l> n ≅ n' : _ | LRNat_ l NNN]< wl > ->
  W[Γ ||-<l> tAlpha n ≅ tAlpha n': _ | LogtoW (LRNat_ l NNN)]< wl >.
Proof.
  intros Hn Hn' Heq.
  pose (Help1 := alphaRed_auxnatred _ Hn 0).
  pose (Help2 := alphaRed_aux (l := l) _ Hn 0) ; cbn in *.
  pose (Help3 := alphaRed_auxnatred _ Hn' 0).
  pose (Help4 := alphaRed_aux (l := l) _ Hn' 0) ; cbn in *.
  pose (Help5 := alphaRedEq_aux (l := l) _ _ Hn Hn' Heq 0).
  eapply WtransEqTerm; [ | eapply WtransEqTerm, WLRTmEqSym].
  2: eassumption.
  all: eapply WredwfSubstTerm ; cycle 1 ; eassumption.
Qed.

Lemma WalphaRedEq {wl Γ l n n'} {NNN : [Γ ||-Nat tNat]< wl >}:
  W[Γ ||-<l> n : _ | LogtoW (LRNat_ l NNN)]< wl > ->
  W[Γ ||-<l> n' : _ | LogtoW (LRNat_ l NNN)]< wl > ->
  W[Γ ||-<l> n ≅ n' : _ | LogtoW (LRNat_ l NNN)]< wl > ->
  W[Γ ||-<l> tAlpha n ≅ tAlpha n': _ | LogtoW (LRNat_ l NNN)]< wl >.
Proof.
  intros Hn Hn' Hneq.
  eapply (TreeTmEqSplit _); intros wl' Ho Ho'.
  Wirrelevance0 ; [reflexivity | eapply alphaRedEq, Hneq].
  - eapply Hn ; do 2 eapply (over_tree_fusion_l) ; exact Ho.
  - eapply Hn', over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
  - eapply over_tree_fusion_r ; exact Ho.
    Unshelve.
    cbn ; now eapply over_tree_le.
Qed.


Lemma alphaValid {wl Γ l n} (VΓ : [||-v Γ]< wl >) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]< wl >) :
  [Γ ||-v<l> tAlpha n : tNat | VΓ | natValid VΓ]< wl >.
Proof.
  constructor; intros; cbn.
  - instValid Vσ ; unshelve eapply WalphaRed ; eassumption.
  - instAllValid Vσ Vσ' Vσσ'; now eapply WalphaRedEq.
Qed.


Lemma alphacongValid {wl Γ l n n'} (VΓ : [||-v Γ]< wl >) 
  (Vn : [Γ ||-v<l> n : tNat | VΓ | natValid VΓ]< wl >)
  (Vn' : [Γ ||-v<l> n' : tNat | VΓ | natValid VΓ]< wl >)
  (Veqn : [Γ ||-v<l> n ≅ n' : tNat | VΓ | natValid VΓ]< wl >) :
  [Γ ||-v<l> tAlpha n ≅ tAlpha n' : tNat | VΓ | natValid VΓ]< wl >.
Proof.
  constructor; intros; cbn; instValid Vσ; now eapply WalphaRedEq.
Qed.

Lemma nSucc_subst :
  forall n t (σ : nat -> term), (nSucc n t)[σ] = nSucc n t[σ].
Proof.
  induction n ; cbn in * ; [reflexivity | ].
  intros ; now rewrite IHn.
Qed.

Lemma alphacongValidSubst {wl Γ n b} (VΓ : [||-v Γ]< wl >) (Hin : in_LCon wl n b) :
  [Γ ||-v< one > tAlpha (nat_to_term n) ≅ nat_to_term b : tNat | VΓ | natValid VΓ ]< wl >.
Proof.
  unshelve econstructor.
  intros ; eapply WredSubstTerm.
  - unfold nat_to_term.
    rewrite nSucc_subst ; cbn.
    unshelve eapply WnSucc_Red, zeroValid ; cycle 2 ; eassumption.
  - cbn ; unfold nat_to_term.
    do 2 rewrite nSucc_subst ; cbn.
    unshelve eapply redtm_alpha ; [assumption | ].
    now eapply f.
Qed.    

  
(*
Lemma elimSuccHypTy_subst {P} σ :
  elimSuccHypTy P[up_term_term σ] = (elimSuccHypTy P)[σ].
Proof.
  unfold elimSuccHypTy.
  cbn. rewrite shift_up_eq.
  rewrite liftSubstComm. cbn. 
  now rewrite up_liftSubst_eq.
Qed.


Lemma liftSubst_singleSubst_eq {t u v: term} : t[u]⇑[v..] = t[u[v..]..].
Proof. now bsimpl. Qed.
*)

Definition boolElim {wl Γ A} (P ht hf : term) {n} {NA : [Γ ||-Bool A]< wl >} (p : BoolProp NA n) : term.
Proof.
  destruct p.
  - exact ht.
  - exact hf. 
  - exact (tBoolElim P ht hf ne).
Defined.

Section BoolElimRed.
  Context {wl Γ l P ht hf}
    (wfΓ : [|- Γ]< wl >)
    (NB : [Γ ||-Bool tBool]< wl >)
    (RB := (LRBool_ _ NB))
    (RP : [Γ,, tBool ||-<l> P]< wl >)
    (RPpt : forall n, [Γ ||-<l> n : _ | RB]< wl > -> W[Γ ||-<l> P[n..]]< wl >)
    (RPext : forall n n' (Rn : [Γ ||-<l> n : _ | RB]< wl >),
      [Γ ||-<l> n' : _ | RB]< wl > ->
      [Γ ||-<l> n ≅ n' : _ | RB]< wl > ->
      W[Γ ||-<l> P[n..] ≅ P[n'..] | RPpt _ Rn]< wl >)
    (RPt := RPpt _ (trueRed wfΓ))
    (RPf := RPpt _ (falseRed wfΓ))
    (Rht : W[Γ ||-<l> ht : P[tTrue..] | RPt]< wl >) 
    (Rhf : W[Γ ||-<l> hf : P[tFalse..] | RPf]< wl >).

  Definition boolRedElimStmt :=
    (forall n (Rn : [Γ ||-<l> n : _ | RB]< wl >), 
      W[Γ ||-<l> tBoolElim P ht hf n : _ | RPpt _ Rn ]< wl > ×
       W[Γ ||-<l> tBoolElim P ht hf n ≅ tBoolElim P ht hf (BoolRedTm.nf Rn) : _ | RPpt _ Rn]< wl >).
  (*×
    (forall n (Nn : BoolProp NB n) (Rn : [Γ ||-<l> n : _ | RB]< wl >), 
      W[Γ ||-<l> tBoolElim P ht hf n : _ | RPpt _ Rn ]< wl > ×
      W[Γ ||-<l> tBoolElim P ht hf n ≅ boolElim P ht hf Nn : _ | RPpt _ Rn]< wl >).
*)
  Lemma boolElimRedAux : boolRedElimStmt.
  Proof.
    escape ; Wescape.
    intros n [? nf red ? nfprop]. 
    assert [Γ ||-<l> nf : _ | RB]< wl >.
    1:{
      econstructor; tea.
      eapply redtmwf_refl; gen_typing.
    }
    eapply WredSubstTerm ; cbn.
    eapply WLRTmRedConv ; [ eapply RPext, LRTmEqSym | ].
    1,2: eapply redwfSubstTerm; now tea.
    2: eapply redtm_boolElim ; now gen_typing.
    Unshelve. 2: assumption.
    induction nfprop.
    - cbn ; eapply WredSubstTerm ; [Wirrelevance0 ; [ reflexivity | exact Rht ] | ].
      eapply redtm_boolElimTrue ; gen_typing.
    - cbn ; eapply WredSubstTerm ; [Wirrelevance0 ; [ reflexivity | exact Rhf ] | ].
      eapply redtm_boolElimFalse ; now gen_typing.
    - destruct r ; cbn.
      unshelve eapply (Wreflect _ _ (tBoolElim P ht hf ne)).
      + apply Wcompleteness.
      + now eapply ty_boolElim. 
      + now eapply ty_boolElim. 
      + eapply convneu_boolElim; tea.
        { eapply escapeEq, reflLRTyEq. }
        { now eapply WescapeEqTerm, WreflLRTmEq. }
        { eapply WescapeEqTerm; now eapply WreflLRTmEq. }
        Unshelve.
        * exact l.
        * assumption.
  Qed.

  Lemma boolElimRed : forall n (Rn : [Γ ||-<l> n : _ | RB]< wl >), W[Γ ||-<l> tBoolElim P ht hf n : _ | RPpt _ Rn ]< wl >.
  Proof. intros. apply (boolElimRedAux). Qed.
End BoolElimRed.


Section BoolElimRedEq.
  Context {wl Γ l P Q ht ht' hf hf'}
    (wfΓ : [|- Γ]< wl >)
    (NB : [Γ ||-Bool tBool]< wl >)
    (RB := LRBool_ _ NB)
    (RP : [Γ,, tBool ||-<l> P]< wl >)
    (RQ : [Γ,, tBool ||-<l> Q]< wl >)
    (eqPQ : [Γ,, tBool |- P ≅ Q]< wl >)
    (RPpt : forall b, [Γ ||-<l> b : _ | RB]< wl > -> W[Γ ||-<l> P[b..]]< wl >)
    (RQpt : forall b, [Γ ||-<l> b : _ | RB]< wl > -> W[Γ ||-<l> Q[b..]]< wl >)
    (RPQext : forall b b' (Rb : [Γ ||-<l> b : _ | RB]< wl >),
      [Γ ||-<l> b' : _ | RB]< wl > ->
      [Γ ||-<l> b ≅ b' : _ | RB]< wl > ->
      W[Γ ||-<l> P[b..] ≅ Q[b'..] | RPpt _ Rb]< wl >)
    (RPt := RPpt _ (trueRed wfΓ))
    (RQt := RQpt _ (trueRed wfΓ))
    (Rht : W[Γ ||-<l> ht : P[tTrue..] | RPt]< wl >) 
    (RQht : W[Γ ||-<l> ht' : Q[tTrue..] | RQt]< wl >) 
    (RPQht : W[Γ ||-<l> ht ≅ ht' : _ | RPt]< wl >)
    (RPf := RPpt _ (falseRed wfΓ))
    (RQf := RQpt _ (falseRed wfΓ))
    (Rhf : W[Γ ||-<l> hf : _ | RPf]< wl >)
    (RQhf : W[Γ ||-<l> hf' : _ | RQf]< wl >)
    (RPQhf : W[Γ ||-<l> hf ≅ hf' : _ | RPf ]< wl >)
    .

  Lemma RPext : forall b b' (Rb : [Γ ||-<l> b : _ | RB]< wl >),
      [Γ ||-<l> b' : _ | RB]< wl > ->
      [Γ ||-<l> b ≅ b' : _ | RB]< wl > ->
      W[Γ ||-<l> P[b..] ≅ P[b'..] | RPpt _ Rb]< wl >.
  Proof.
    intros. eapply WtransEq; [| eapply WLRTyEqSym ]; eapply RPQext; cycle 1; tea.
    now eapply reflLRTmEq.
    Unshelve. 2,3: eauto.
  Qed.

  Lemma boolElimRedAuxLeft : @boolRedElimStmt _ _ _ P ht hf NB RPpt.
  Proof.
    eapply boolElimRedAux; tea.
    + eapply RPext.
  Qed.

  Lemma boolElimRedAuxRight : @boolRedElimStmt _ _ _ Q ht' hf' NB RQpt.
  Proof.
    eapply boolElimRedAux; tea.
    + intros. eapply WtransEq; [eapply WLRTyEqSym |]; eapply RPQext; cycle 1; tea.
      now eapply reflLRTmEq.
    Unshelve. all:tea.
  Qed.

  Lemma boolElimRedEqAux :
    (forall b b' (Rbb' : [Γ ||-<l> b ≅ b' : _ | RB]< wl >) (Rb : [Γ ||-<l> b : _ | RB]< wl >) (Rb' : [Γ ||-<l> b' : _ | RB]< wl >), 
        W[Γ ||-<l> tBoolElim P ht hf b ≅ tBoolElim Q ht' hf' b' : _ | RPpt _ Rb ]< wl >).
    (*×
    (forall b b' (Rbb' : BoolPropEq NB b b') (Rb : [Γ ||-<l> b : _ | RB]< wl >) (Rb' : [Γ ||-<l> b' : _ | RB]< wl >), 
      W[Γ ||-<l> tBoolElim P ht hf b ≅ tBoolElim Q ht' hf' b' : _ | RPpt _ Rb ]< wl >) *)
  Proof.
    escape ; Wescape.
    intros b b' [?? nfL nfR redL redR eq prop] Rt Ru.
    destruct (BoolPropEq_whnf prop).
    assert [Γ ||-<l> nfL : _ | RB]< wl > by (eapply redTmFwd ; cycle 1; tea).
    assert [Γ ||-<l> nfR : _ | RB]< wl > by (eapply redTmFwd; cycle 1; tea).
    eapply WLREqTermHelper.
    1: now eapply (boolElimRedAuxLeft).
    1: now eapply (boolElimRedAuxRight).
    1: eapply RPQext ; [ tea | ] ; now econstructor.
    eapply WLRTmEqRedConv.
    1: eapply RPext; tea. 
    1: eapply LRTmEqSym; eapply redwfSubstTerm; cycle 1; now tea.
    unshelve erewrite (redtmwf_det _ _ (BoolRedTm.red Rt) redL); tea.
    1: dependent inversion Rt; subst; cbn; now eapply BoolProp_whnf.
    unshelve erewrite (redtmwf_det _ _ (BoolRedTm.red Ru) redR); tea.
    1: dependent inversion Ru; subst; cbn; now eapply BoolProp_whnf.
    Unshelve.
    2:assumption.
    induction prop.
    - eapply WtransEqTerm; [ | eapply WtransEqTerm, WLRTmEqSym].
      2: now Wirrelevance0. 
      + eapply WredSubstTerm ; [now Wirrelevance0 | ].
        now eapply redtm_boolElimTrue.
      + eapply WLRTmEqRedConv.
        2: eapply WredSubstTerm ; [now Wirrelevance0 | ].
        * eapply WLRTyEqSym, RPQext ; auto.
          now eapply reflLRTmEq.
        * now eapply redtm_boolElimTrue.
    - eapply WtransEqTerm; [ | eapply WtransEqTerm, WLRTmEqSym].
      2: now Wirrelevance0. 
      + eapply WredSubstTerm ; [now Wirrelevance0 | ].
        now eapply redtm_boolElimFalse.
      + eapply WLRTmEqRedConv.
        2: eapply WredSubstTerm ; [now Wirrelevance0 | ].
        * eapply WLRTyEqSym, RPQext ; auto.
          now eapply reflLRTmEq.
        * now eapply redtm_boolElimFalse.
    - escape ; Wescape.
      assert [Γ |- P[ne..] ≅ Q[ne'..]]< wl >. 1:{
        eapply WescapeEq. eapply RPQext; tea.
        econstructor.
        1,2: now eapply redtmwf_refl.
        2: now constructor.
        gen_typing.
      }
      eapply WneuTermEq.
      + eapply ty_boolElim; tea.
      + eapply ty_conv. 
        1: eapply ty_boolElim; tea.
        now symmetry.
      + eapply convneu_boolElim ; tea.
        now destruct r.
        Unshelve. all: tea.
Qed.

  Lemma boolElimRedEq :
    (forall b b' (Rbb' : [Γ ||-<l> b ≅ b' : _ | RB]< wl >) (Rb : [Γ ||-<l> b : _ | RB]< wl >) (Rb' : [Γ ||-<l> b' : _ | RB]< wl >), 
      W[Γ ||-<l> tBoolElim P ht hf b ≅ tBoolElim Q ht' hf' b' : _ | RPpt _ Rb ]< wl >).
  Proof. apply boolElimRedEqAux. Qed.
End BoolElimRedEq.


Section BoolElimValid.
  Context {wl Γ l P}
    (VΓ : [||-v Γ]< wl >)
    (VB := boolValid (l:=l) VΓ)
    (VΓB := validSnoc' VΓ VB)
    (VP : [Γ ,, tBool ||-v<l> P | VΓB]< wl >).

  Context {ht hf}
    (VPt := substS VP (trueValid VΓ))
    (VPf := substS VP (falseValid VΓ))
    (Vht : [Γ ||-v<l> ht : P[tTrue..] | VΓ | VPt]< wl >) 
    (Vhf : [Γ ||-v<l> hf : P[tFalse..] | VΓ | VPf]< wl >).

  Lemma boolElimValid {b}
    (Vb : [Γ ||-v<l> b : tBool | VΓ | VB]< wl >)
    (VPb := substS VP Vb)
    : [Γ ||-v<l> tBoolElim P ht hf b : _ | VΓ | VPb]< wl >.
  Proof.
    constructor; intros.
    - instValid Vσ; cbn.
      epose proof (Vuσ := liftSubstS' VB Vσ).
      unshelve eapply TreeTmSplit ; [eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve | ].
      intros wl'' Ho HA.
      pose (f':= over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      instValid Vuσ; escape ; Wescape.
      unshelve eapply boolElimRed; tea.
      + econstructor ; eapply redtywf_refl, wft_term.
        now eapply ty_bool, wfc_Ltrans.
      + intros m Rm.
        rewrite up_single_subst.
        unshelve eapply validTy.
        6: eassumption.
        * now eapply wfLCon_le_trans.
        * now eapply wfc_Ltrans.
        * unshelve econstructor ; [ | now eapply TmLogtoW].
          now bsimpl ; unshelve eapply subst_Ltrans.
      + cbn.
        set (Help := {|  BoolRedTy.red := redtywf_refl (wft_term (ty_bool (wfc_Ltrans f' wfΔ))) |}).
        change [Δ ||-< l > b[σ] : tBool | LRBool_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVb.
        1: eapply over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
        eapply over_tree_fusion_r ; exact Ho.
      + now eapply wfc_Ltrans.
      + eapply RVP ; do 2 eapply (over_tree_fusion_l).
        exact Ho.
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt ; cycle 2 ; tea.
        1: now eapply wfLCon_le_trans.
        1: now eapply wfc_Ltrans.
        1,2: unshelve econstructor; [bsimpl ; now unshelve eapply subst_Ltrans| cbn].
        1,2: now eapply TmLogtoW.
        unshelve econstructor; [ | cbn].
        * fsimpl; cbn; now unshelve eapply reflSubst.
        * now eapply TmEqLogtoW.
      + Wirrelevance0.
        2: eapply WTm_Ltrans ; eassumption.
        now bsimpl.
      + Wirrelevance0.
        2: eapply WTm_Ltrans ; eassumption.
        now bsimpl.
        Unshelve.
        all: eassumption.
    - instAllValid Vσ Vσ' Vσσ'.
      pose (Vuσ := liftSubstS' VB Vσ).
      pose proof (Vuσ' := liftSubstS' VB Vσ').
      pose proof (Vuσrea :=  liftSubstSrealign' VB Vσσ' Vσ').
      pose proof (Vuσσ' := liftSubstSEq' VB Vσσ').
      instValid Vuσ'; instAllValid Vuσ Vuσrea Vuσσ'; escape ; Wescape.
      unshelve eapply TreeTmEqSplit ; [do 3 (eapply DTree_fusion) ; shelve | ].
      intros wl'' Ho HA.
      pose (f':= over_tree_le Ho).
      Wirrelevance0.  1: now rewrite singleSubstComm'.
      unshelve eapply boolElimRedEq ; tea; fold subst_term.
      10,11,13,14: Wirrelevance0 ; [ | unshelve eapply WTm_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
      10,11: Wirrelevance0 ; [ | unshelve eapply WTmEq_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
      6,7: unshelve eapply validTy ; [ .. | eassumption | ].
      6,8: eassumption.
      4: now eapply wfc_Ltrans.
      + econstructor ; eapply redtywf_refl, wft_term.
        now eapply ty_bool, wfc_Ltrans.
      + cbn ; intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 4; tea.
        2: unshelve econstructor; [| now eapply TmLogtoW].
        1: unshelve eapply subst_Ltrans ; [ .. | eassumption | | eassumption].
      + cbn.
        set (Help := {| BoolRedTy.red := _ |}).
        change [Δ ||-< l > b[σ] : tBool | LRBool_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVb.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
      + cbn. intros m Rm.
        rewrite up_single_subst. 
        unshelve eapply validTy; cycle 4; tea.
        2: unshelve econstructor; [| now eapply TmLogtoW].
        1: unshelve eapply subst_Ltrans ; [ .. | eassumption | | eassumption].
      + do 3 eapply (over_tree_fusion_l) ; exact Ho.
      + eapply over_tree_fusion_r  ; do 2 eapply (over_tree_fusion_l); exact Ho.
      + now eapply convty_Ltrans.
      + intros m m' Rm Rm' Rmm'; cbn.
        Wirrelevance0. 1: now rewrite up_single_subst.
        rewrite up_single_subst.
        unshelve eapply validTyExt ; cycle 3 ; tea.
        2: now eapply wfc_Ltrans.
        2,3: unshelve econstructor; [| now eapply TmLogtoW].
        2,3: unshelve eapply subst_Ltrans ; [ .. | eassumption] ; eassumption.
        unshelve econstructor; [|now eapply TmEqLogtoW].
        bsimpl.
        now unshelve eapply eqsubst_Ltrans.
      + cbn.
        set (Help := {| BoolRedTy.red := _ |}).
        change [Δ ||-< l > b[σ] ≅ b[σ'] : tBool | LRBool_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply REVb.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        do 2 eapply over_tree_fusion_r ; eapply over_tree_fusion_l ; exact Ho.
      + cbn.
        set (Help := {| BoolRedTy.red := _ |}).
        change [Δ ||-< l > b[σ'] : tBool | LRBool_ _ Help ]< wl'' >.
        irrelevanceRefl.
        unshelve eapply RVb0.
        1: eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
        Unshelve. all: now constructor.
Qed.    

  Lemma boolElimTrueValid  : 
    [Γ ||-v<l> tBoolElim P ht hf tTrue ≅ ht : _ | VΓ | VPt]< wl >.
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VB Vσ).
    instValid Vσ; instValid Vuσ; escape ; Wescape.
    unshelve eapply TreeTmEqSplit ; [eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve | ].
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    Wirrelevance0.  1: now rewrite singleSubstComm'.
    eapply WtransEqTerm.
    1: unshelve eapply ((boolElimRedAux _ _ _ _ _ _ _ _) (Build_BoolRedTm _ _ _ BoolRedTm.trueR)) ; tea; fold subst_term.
    2: econstructor ; eapply  (redtywf_refl (wft_term (ty_bool (wfc_Ltrans f' wfΔ)))).
    1: now eapply wfc_Ltrans.
    1: unshelve eapply (WRed _ (validTy VP _ _ Vuσ)).
    1: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    + intros m Rm.
      rewrite up_single_subst. 
      unshelve eapply validTy ; cycle 5 ; tea.
      3: now eapply wfc_Ltrans.
      unshelve econstructor; [now eapply subst_Ltrans | ].
      now eapply TmLogtoW.
    + intros m m' Rm Rm' Rmm'; cbn.
      Wirrelevance0. 1: now rewrite up_single_subst.
      rewrite up_single_subst.
      unshelve eapply validTyExt ; cycle 3.
      1: eassumption.
      3: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      1: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans | now eapply TmEqLogtoW].
      bsimpl; cbn; eapply reflSubst.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVht.
      now bsimpl.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVhf.
      now bsimpl.
    + now eapply redtmwf_refl, ty_true, wfc_Ltrans.
    + now eapply convtm_true, wfc_Ltrans.
    + fold subst_term ; Wirrelevance0 ; [reflexivity | ].
      cbn.
      eapply WTmEq_Ltrans, WredwfSubstTerm.
      1: Wirrelevance0 ; [ | eassumption] ; now bsimpl.
      eapply redtmwf_boolElimTrue ; auto .
      all: eapply typing_meta_conv ; [eassumption | now bsimpl ].
      Unshelve.
      1,2: now constructor.
      all: try eassumption.
      enough (Hyp: P[up_term_term σ][tTrue..] = P[tTrue..][σ]) by (rewrite Hyp ; eassumption).
      now bsimpl.
  Qed.

  Lemma boolElimFalseValid  : 
    [Γ ||-v<l> tBoolElim P ht hf tFalse ≅ hf : _ | VΓ | VPf]< wl >.
  Proof.
    constructor; intros.
    epose proof (Vuσ := liftSubstS' VB Vσ).
    instValid Vσ; instValid Vuσ; escape ; Wescape.
    unshelve eapply TreeTmEqSplit ; [eapply DTree_fusion ; [eapply DTree_fusion | ] ; shelve | ].
    intros wl'' Ho HA.
    pose (f':= over_tree_le Ho).
    Wirrelevance0.  1: now rewrite singleSubstComm'.
    eapply WtransEqTerm.
    1: unshelve eapply ((boolElimRedAux _ _ _ _ _ _ _ _) (Build_BoolRedTm _ _ _ BoolRedTm.falseR)) ; fold subst_term.
    2: econstructor ; eapply  (redtywf_refl (wft_term (ty_bool (wfc_Ltrans f' wfΔ)))).
    1: now eapply wfc_Ltrans.
    1: unshelve eapply (WRed _ (validTy VP _ _ Vuσ)).
    1: eapply over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    + intros m Rm.
      rewrite up_single_subst. 
      unshelve eapply validTy ; cycle 5 ; tea.
      3: now eapply wfc_Ltrans.
      unshelve econstructor; [now eapply subst_Ltrans | ].
      now eapply TmLogtoW.
    + intros m m' Rm Rm' Rmm'; cbn.
      Wirrelevance0. 1: now rewrite up_single_subst.
      rewrite up_single_subst.
      unshelve eapply validTyExt ; cycle 3.
      1: eassumption.
      3: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      1: unshelve econstructor; [now eapply subst_Ltrans | now eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans | now eapply TmEqLogtoW].
      bsimpl; cbn; eapply reflSubst.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVht.
      now bsimpl.
    + Wirrelevance0.
      2: eapply WTm_Ltrans.
      2: now eapply RVhf.
      now bsimpl.
    + now eapply redtmwf_refl, ty_false, wfc_Ltrans.
    + now eapply convtm_false, wfc_Ltrans.
    + fold subst_term ; Wirrelevance0 ; [reflexivity | ].
      cbn.
      eapply WTmEq_Ltrans, WredwfSubstTerm.
      1: Wirrelevance0 ; [ | eassumption ] ; now bsimpl.
      eapply redtmwf_boolElimFalse ; auto .
      all: eapply typing_meta_conv ; [eassumption | now bsimpl ].
      Unshelve.
      1,2: now constructor.
      all: try eassumption.
      enough (Hyp: P[up_term_term σ][tFalse..] = P[tFalse..][σ]) by (rewrite Hyp ; eassumption).
      now bsimpl.
  Qed.

End BoolElimValid.

Lemma boolElimCongValid {wl Γ l P Q ht ht' hf hf' b b'}
    (VΓ : [||-v Γ]< wl >)
    (VB := boolValid (l:=l) VΓ)
    (VΓB := validSnoc' VΓ VB)
    (VP : [Γ ,, tBool ||-v<l> P | VΓB]< wl >)
    (VQ : [Γ ,, tBool ||-v<l> Q | VΓB]< wl >)
    (VPQ : [Γ ,, tBool ||-v<l> P ≅ Q | VΓB | VP]< wl >)
    (VPt := substS VP (trueValid VΓ))
    (VQt := substS VQ (trueValid VΓ))
    (Vht : [Γ ||-v<l> ht : P[tTrue..] | VΓ | VPt]< wl >) 
    (Vht' : [Γ ||-v<l> ht' : Q[tTrue..] | VΓ | VQt]< wl >)
    (Vheqt : [Γ ||-v<l> ht ≅ ht' : P[tTrue..] | VΓ | VPt]< wl >)
    (VPf := substS VP (falseValid VΓ))
    (VQf := substS VQ (falseValid VΓ))
    (Vhf : [Γ ||-v<l> hf : _ | VΓ | VPf]< wl >) 
    (Vhf' : [Γ ||-v<l> hf' : _ | VΓ | VQf]< wl >)
    (Vheqf : [Γ ||-v<l> hf ≅ hf' : _ | VΓ | VPf]< wl >) 
    (Vb : [Γ ||-v<l> b : _ | VΓ | VB]< wl >)
    (Vb' : [Γ ||-v<l> b' : _ | VΓ | VB]< wl >)
    (Veqb : [Γ ||-v<l> b ≅ b' : _ | VΓ | VB]< wl >)
    (VPb := substS VP Vb) :
    [Γ ||-v<l> tBoolElim P ht hf b ≅ tBoolElim Q ht' hf' b' : _ | VΓ | VPb]< wl >.
Proof.
  constructor; intros.
  pose (Vuσ := liftSubstS' VB Vσ).
  instValid Vσ; instValid Vuσ; escape ; Wescape.
  unshelve eapply TreeTmEqSplit.
  1: do 2 eapply DTree_fusion ; [eapply DTree_fusion | eapply DTree_fusion | ..] ; shelve.
  intros wl'' Ho HA.
  pose (f':= over_tree_le Ho).
  Wirrelevance0.  1: now rewrite singleSubstComm'.
  unshelve eapply boolElimRedEq; tea; fold subst_term.
  1: econstructor ; eapply  (redtywf_refl (wft_term (ty_bool (wfc_Ltrans f' wfΔ)))).

  9,10,12,13: Wirrelevance0 ; [ | unshelve eapply WTm_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
  9,10: Wirrelevance0 ; [ | unshelve eapply WTmEq_Ltrans ; cycle 3 ; eassumption] ; now bsimpl.
  5,6: unshelve eapply validTy ; [ .. | eassumption | ].
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    1: now eapply wfc_Ltrans.
    now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
  + irrelevanceRefl.
    unshelve eapply RVb.
    1: eapply over_tree_fusion_l, over_tree_fusion_l, over_tree_fusion_l ; exact Ho.
    eapply over_tree_fusion_r, over_tree_fusion_l, over_tree_fusion_l; exact Ho.
  + now eapply wfc_Ltrans.
  + intros m Rm.
    rewrite up_single_subst. 
    unshelve eapply validTy; cycle 4; tea.
    1: now eapply wfc_Ltrans.
    now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
  + eassumption.
  + eapply over_tree_fusion_l, over_tree_fusion_r ; exact Ho.
  + eassumption.
  + eapply over_tree_fusion_r, over_tree_fusion_r ; exact Ho.
  + now eapply convty_Ltrans.
  + intros m m' Rm Rm' Rmm'; cbn.
    Wirrelevance0. 1: now rewrite up_single_subst.
    rewrite up_single_subst.
    eapply WtransEq; cycle 1.
    * unshelve eapply validTyEq.
      9: eassumption.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
    * unshelve eapply validTyExt; cycle 3 ; tea.
      1: now eapply wfLCon_le_trans.
      1: now eapply wfc_Ltrans.
      1,2: now unshelve econstructor; [eapply subst_Ltrans| eapply TmLogtoW].
      unshelve econstructor; [eapply eqsubst_Ltrans| now eapply TmEqLogtoW].
      bsimpl. eapply reflSubst.
  + irrelevance0 ; [ | eapply (WRedTmEq _ RVeqb)].
    reflexivity.
    eapply over_tree_fusion_l, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
  + irrelevance0 ; [ | eapply (WRedTm _ RVb')].
    reflexivity.
    eapply over_tree_fusion_r, over_tree_fusion_r, over_tree_fusion_l ; exact Ho.
    Unshelve.
    all: tea.
    all: now eapply wfc_Ltrans.
Qed.

End Bool.
