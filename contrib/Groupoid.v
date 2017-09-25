Require Import HoTT.Basics.

Delimit Scope groupoid_scope with groupoid.

Local Open Scope groupoid_scope.

Section groupoid.
  Variable A : Type.
  Variable (R : A -> A -> Type).
  Context {A_set : IsHSet A} 
          {R_HSet : forall x y, IsHSet (R x y)}
          {R_refl : Reflexive R}
          {R_trans : Transitive R}
          {R_symm : Symmetric R}.


  Local Notation "g 'o' f" := (transitivity f g) : groupoid_scope.
  Local Notation "1" := (reflexivity _) : groupoid_scope.
  Local Notation "f ^" := (symmetry _ _ f) : groupoid_scope.

  Record groupoid := { g_1_l : forall {x y} (f : R x y), 1 o f = f
                     ; g_1_r : forall {x y} (f : R x y), f o 1 = f
                     ; g_assoc : forall {x y z w} (f : R x y) (g : R y z) (h : R z w),
                                 h o (g o f) = (h o g) o f
                     ; g_V_r : forall {x y} (f : R x y), f o f^ = 1
                     ; g_V_l : forall {x y} (f : R x y), f^ o f = 1
                     }.

  Lemma g_V_V : forall (G : groupoid) x y (f : R x y), f^^ = f.
  Proof.
    intros.
    transitivity (f^^ o (f^ o f)).
    - transitivity (f^^ o 1).
      * apply (g_1_r G _)^.
      * apply (ap (fun z => f^^ o z)).
        refine (g_V_l G _)^.
    - refine (_ o g_assoc G _ _ _).
      transitivity (1 o f); [ | apply (g_1_l G)].
      apply (ap (fun z => z o f)).
      apply (g_V_l G f^).
  Qed.

  Lemma inv_eq : forall (G : groupoid) x y (f : R x y) (g : R y x),
        f o g = 1 <-> f^ = g.
  Proof.
    intros.
    split; intros eq.
    - transitivity (f^ o 1); [ apply (g_1_r G _)^ | ].
      rewrite <- eq.
      rewrite (g_assoc G).
      rewrite (g_V_l G).
      apply (g_1_l G).
    - rewrite <- eq.
      apply (g_V_r G).
  Qed.

  Definition cmp_eq : forall {x1 x2 x3} {f f' : R x1 x2} {g g' : R x2 x3},
             f = f' -> g = g' -> g o f = g' o f'.
  Proof.
    intros x1 x2 x3 f f' g g' H_f H_g.
    rewrite H_f.
    rewrite H_g.
    reflexivity.
  Defined.
  Local Infix "oo" := cmp_eq (at level 30) : groupoid_scope.


  Lemma inv_compose : forall (G : groupoid) {x y z} (f : R x y) (g : R y z),
        (g o f)^ = f^ o g^.
  Proof.
    intros.
    apply inv_eq.
    refine (_ o (g_assoc G _ _ _)^).
    rewrite (g_assoc G g^ f^ f).
    rewrite (g_V_r G).
    rewrite (g_1_l G).
    apply (g_V_r G).
  Qed.


End groupoid.

Close Scope groupoid_scope.

Module Export GroupoidNotations.
  Notation "g 'o' f" := (transitivity f g) : groupoid_scope.
  Notation "1" := (reflexivity _) : groupoid_scope.
  Notation "f ^" := (symmetry _ _ f) : groupoid_scope.
End GroupoidNotations.

  
