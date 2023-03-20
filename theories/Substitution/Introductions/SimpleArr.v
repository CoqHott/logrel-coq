From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance.
From LogRel.Substitution Require Import Irrelevance Properties.
From LogRel.Substitution.Introductions Require Import Universe Pi Application.

Set Universe Polymorphism.

Section SimpleArrValidity.

  Context `{GenericTypingProperties}.

  Lemma simpleArrValid {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ||-v< l > G | VΓ]) : 
    [Γ ||-v<l> arr F G | VΓ].
  Proof.
    unshelve eapply PiValid; tea.
    replace G⟨↑⟩ with G⟨@wk1 Γ anDummy F⟩ by now bsimpl.
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
    + replace G⟨↑⟩ with G⟨@wk1 Γ anDummy F⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ anDummy F'⟩ by now bsimpl.
      now eapply wk1ValidTy.
    + replace G'⟨↑⟩ with G'⟨@wk1 Γ anDummy F⟩ by now bsimpl.
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


End SimpleArrValidity.


