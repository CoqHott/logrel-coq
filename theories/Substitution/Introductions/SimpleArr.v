From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties Conversion.
From LogRel.Substitution.Introductions Require Import Universe Pi Application Lambda Var.

Set Universe Polymorphism.

Section SimpleArrValidity.

  Context `{GenericTypingProperties}.

  Lemma simpleArrValid {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ||-v< l > G | VΓ]) :
    [Γ ||-v<l> arr F G | VΓ].
  Proof.
    unshelve eapply PiValid; tea.
    replace G⟨↑⟩ with G⟨@wk1 Γ F⟩ by now bsimpl.
    now eapply wk1ValidTy.
  Qed.

  Lemma simpleArrCongValid {l Γ F F' G G'} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VF' : [Γ ||-v< l > F' | VΓ ])
    (VeqF : [Γ ||-v< l > F ≅ F' | VΓ | VF])
    (VG : [Γ ||-v< l > G | VΓ ])
    (VG' : [Γ ||-v< l > G' | VΓ ])
    (VeqG : [Γ ||-v< l > G ≅ G' | VΓ | VG]) :
    [Γ ||-v<l> arr F G ≅ arr F' G' | VΓ | simpleArrValid _ VF VG].
  Proof.
    eapply irrelevanceEq.
    unshelve eapply PiCong; tea.
    + replace G⟨↑⟩ with G⟨@wk1 Γ F⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ F'⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ F⟩ by now bsimpl.
      eapply irrelevanceEq'.
      2: now eapply wk1ValidTyEq.
      now bsimpl.
    Unshelve. 2: tea.
  Qed.

  Lemma simple_appValid {Γ t u F G l}
    (VΓ : [||-v Γ])
    {VF : [Γ ||-v<l> F | VΓ]}
    (VG : [Γ ||-v<l> G | VΓ])
    (VΠ : [Γ ||-v<l> arr F G | VΓ])
    (Vt : [Γ ||-v<l> t : arr F G | _ | VΠ])
    (Vu : [Γ ||-v<l> u : F | _ | VF]) :
    [Γ ||-v<l> tApp t u : G| _ | VG].
  Proof.
    eapply irrelevanceTm'.
    2: eapply appValid; tea.
    now bsimpl.
  Unshelve. all: tea.
  Qed.

  Lemma simple_idValid {Γ A l}
    (VΓ : [||-v Γ])
    {VF : [Γ ||-v<l> A | VΓ]}
    (VΠ : [Γ ||-v<l> arr A A | VΓ]) :
    [Γ ||-v<l> idterm A : arr A A | _ | VΠ].
  Proof.
    eapply irrelevanceTm'.
    2: unshelve eapply lamValid.
    5: unshelve eapply var0Valid.
    - now rewrite wk1_ren_on.
    - tea.
  Qed.

  Lemma simple_compValid {Γ A B C f g l}
    (VΓ : [||-v Γ])
    {VA : [Γ ||-v<l> A | VΓ]}
    (VB : [Γ ||-v<l> B | VΓ])
    (VC : [Γ ||-v<l> C | VΓ])
    (VAB : [Γ ||-v<l> arr A B | VΓ])
    (VBC : [Γ ||-v<l> arr B C | VΓ])
    (VAC : [Γ ||-v<l> arr A C | VΓ])
    (Vf : [Γ ||-v<l> f : arr A B | _ | VAB])
    (Vg : [Γ ||-v<l> g : arr B C | _ | VBC]) :
    [Γ ||-v<l> comp A g f : arr A C | _ | VAC].
  Proof.
    eapply irrelevanceTm'.
    2: unshelve eapply lamValid.
    5: unshelve eapply simple_appValid.
    9: unshelve eapply simple_appValid.
    13: eapply var0Valid.
    4: eapply wk1ValidTy; exact VC.
    4: eapply wk1ValidTy; exact VB.
    - now rewrite wk1_ren_on.
    - eassumption.
    - do 2 erewrite wk1_ren_on. rewrite<- arr_ren1.
      erewrite<- wk1_ren_on.
      now eapply wk1ValidTy.
    - eapply irrelevanceTm'. 2: erewrite<- wk1_ren_on;now eapply wk1ValidTm.
      rewrite wk1_ren_on. rewrite arr_ren1.
      do 2 rewrite wk1_ren_on. reflexivity.
    - do 2 erewrite wk1_ren_on. rewrite<- arr_ren1.
      erewrite<- wk1_ren_on.
      now eapply wk1ValidTy.
    - eapply irrelevanceTm'. 2: erewrite<- wk1_ren_on;now eapply wk1ValidTm.
      rewrite wk1_ren_on. rewrite arr_ren1.
      do 2 rewrite wk1_ren_on. reflexivity.

      Unshelve. all: tea.
  Qed.

End SimpleArrValidity.
