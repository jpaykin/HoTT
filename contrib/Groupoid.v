Require Import HoTT.Basics.
(*Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesFunext TruncType.*)
(* How many of these do we actuall need? *)


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

  Record groupoid := { g_1_l : forall x y (f : R x y), 1 o f = f
                     ; g_1_r : forall x y (f : R x y), f o 1 = f
                     ; g_assoc : forall x y z w (f : R x y) (g : R y z) (h : R z w),
                                 h o (g o f) = (h o g) o f
                     ; g_V_r : forall x y (f : R x y), f o f^ = 1
                     ; g_V_l : forall x y (f : R x y), f^ o f = 1
                     }.


End groupoid.

Close Scope groupoid_scope.

Module Export GroupoidNotations.
  Notation "g 'o' f" := (transitivity f g) : groupoid_scope.
  Notation "1" := (reflexivity _) : groupoid_scope.
  Notation "f ^" := (symmetry _ _ f) : groupoid_scope.
End GroupoidNotations.

  
