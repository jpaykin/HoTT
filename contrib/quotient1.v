(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics.
(*Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesFunext TruncType.
Require Import HIT.epi HIT.Truncations HIT.Connectedness.*)
Require Import Groupoid.


(** * Quotient of a Type by a groupoid 

We aim to model:
<<
Inductive quotient1 : Type :=
   | point : A -> quotient1
   | cell : forall x y, morphism x y -> point x = point y
   | cell_compose : forall x y z (f : morphism x y) (g : morphism y z),
                    cell (g o f) = cell f @ cell g
   | quotient1_trunc : IsTrunc 1 quotient1
>>
*)

Module Export Quotient1.
Section Domain.
  Variable A : Type.
  Variable R : A -> A -> Type.
  Context {A_set : IsHSet A} 
          {R_HSet : forall x y, IsHSet (R x y)}
          {R_refl : Reflexive R}
          {R_trans : Transitive R}
          {R_symm : Symmetric R}.
  Variable G : groupoid A R.

  Local Open Scope groupoid_scope.

  Private Inductive quotient1 : Type :=
  | point : A -> quotient1
  .
  Axiom cell : forall {x y}, R x y -> point x = point y.
  Axiom cell_compose : forall {x y z} (f : R x y) (g : R y z),
        cell (g o f)%groupoid = cell f @ cell g.
  Axiom quotient1_trunc : IsTrunc 1 quotient1.
  Global Existing Instance quotient1_trunc.

  Section quotient1_ind.

    Variable P : quotient1 -> Type.
    Context {P_1Type : forall a, IsTrunc 1 (P a)}.
    Variable P_point : forall x, P (point x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.
    Variable P_compose : forall x y z (f : R x y) (g : R y z),
             P_cell _ _ (g o f)
           = transport2 P (cell_compose f g) (P_point x)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell _ _ f)
           @ P_cell _ _ g).

    Definition quotient1_ind (a : quotient1) : P a :=
      ( match a with
        | point x => fun _ _ _ => P_point x
        end ) P_1Type P_cell P_compose.
    Axiom quotient1_ind_cell : forall {x y} (f : R x y),
          apD quotient1_ind (cell f) = P_cell _ _ f.

    Let quotient1_ind_compose' : forall {x y z} (f : R x y) (g : R y z),
        apD quotient1_ind (cell (g o f))
      = transport2 P (cell_compose f g) (quotient1_ind (point x))
      @ apD quotient1_ind (cell f @ cell g).
    Proof.
      intros.
      refine (quotient1_ind_cell (g o f) @ _).
      refine (P_compose _ _ _ f g @ _).
      refine (1 @@ _).
      refine (1 @@ ap _ (quotient1_ind_cell f)^ @@ (quotient1_ind_cell g)^ @ _).
      refine (apD_pp _ _ _)^.
    Defined.


    Axiom quotient1_ind_compose : forall x y z (f : R x y) (g : R y z),
          apD02 quotient1_ind (cell_compose f g)
        = quotient1_ind_compose' f g.


  End quotient1_ind.

Lemma transport_const_pp : forall {A B} {x1 x2 x3 : A} (p : x1 = x2) (q : x2 = x3) (y : B),
      transport_const (p @ q) y
    = transport_pp (fun _ => B) p q y
    @ (ap _ (transport_const p y)
    @ transport_const q y).
Proof.
  destruct p. destruct q. intros.
  auto.
Qed.


Lemma transport_const_inv : forall {A B} {x1 x2 : A} 
                                   (p : x1 = x2) {y1 y2 : B} (q : y1 = y2),
      transport_const p y1 @ q
    = ap (transport (fun _ => B) p) q 
    @ transport_const p y2.
Proof.
  destruct p; destruct q; auto.
Qed.

Lemma apD_const' : forall {A B} {x y : A} (f : A -> B) (p : x = y),
      ap f p = (transport_const p (f x))^ @ apD f p.
Proof. intros. 
       apply moveL_Vp.
       apply (apD_const _ _)^.
Defined.





  Section quotient1_rec.

    Variable C : Type.
    Variable C_point : A -> C.
    Variable C_cell : forall {x y}, R x y -> C_point x = C_point y.
    Variable C_compose : forall {x y z} (f : R x y) (g : R y z),
      C_cell _ _ (g o f) = C_cell _ _ f @ C_cell _ _ g.
    Context {C_1Type : IsTrunc 1 C}.

    Let C_cell' : forall {x y} (f : R x y), 
      cell f # C_point x = C_point y.
    Proof.
      intros.
      refine (transport_const (cell f) (C_point x) @ C_cell _ _ f).
    Defined. 

    Let C_compose' : forall {x y z} (f : R x y) (g : R y z),
        C_cell' (g o f)
      = transport2 (fun _ => C) (cell_compose f g) (C_point x)
      @ ((transport_pp (fun _ => C) (cell f) (cell g) (C_point x)
      @ ap (transport (fun _ => C) (cell g)) (C_cell' f))
      @ C_cell' g).
    Proof.
      intros.
      unfold C_cell'. 
        refine (transport2_const (cell_compose f g) _ @@ 1 @ _).
        refine (concat_pp_p _ _ _ @ _).
        refine (1 @@ _).
        refine (1 @@ C_compose _ _ _ f g @ _).
        refine (transport_const_pp _ _ _ @@ 1 @ _).
        set (p := transport_pp (fun _ => C) (cell f) (cell g) (C_point x)).
        set (q := C_cell y z g).
        set (r := C_cell x y f).
        refine (_ @ ((1 @@ (ap_pp _ _ _)^) @@ 1)).
        set (s := ap (transport (fun _ => C) (cell g)) (transport_const (cell f) (C_point x))).
        refine (concat_pp_p _ _ _ @ (1 @@ _) @ concat_p_pp _ _ _).
        refine (concat_pp_p _ _ _ @ (1 @@ _) @ concat_p_pp _ _ _).
        refine (concat_p_pp _ _ _ @ (_ @@ 1) @ concat_pp_p _ _ _).        
        apply transport_const_inv.
    Defined.


    Definition quotient1_rec : quotient1 -> C.
    Proof.
      apply quotient1_ind with (P_point := C_point) (P_cell := @C_cell'); intros.
      - exact C_1Type.
      - apply C_compose'.
     Defined.

    Lemma quotient1_rec_cell : forall {x y} (f : R x y),
        ap quotient1_rec (cell f) = C_cell _ _ f.
    Proof.
      intros.
      refine (apD_const' _ _ @ _).
      refine (1 @@ quotient1_ind_cell _ _ _ _ _ @ _).
      unfold C_cell'.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_Vp _ @@ 1 @ _).
      apply concat_1p.
    Qed.



    Let quotient1_rec_compose' : forall {x y z} (f : R x y) (g : R y z),
        ap quotient1_rec (cell (g o f)) = ap quotient1_rec (cell f @ cell g).
    Proof.
      intros.
      refine (_ @ (ap_pp _ _ _)^).
      refine ( quotient1_rec_cell (g o f) 
             @ _ 
             @ ((quotient1_rec_cell f)^ @@ (quotient1_rec_cell g)^)).
      apply C_compose.
    Defined.

    Let quotient1_rec_compose'' : forall {x y z} (f : R x y) (g : R y z),
        apD quotient1_rec (cell (g o f))
      = transport2 (fun _ => C) (cell_compose f g) (quotient1_rec (point x))
      @ apD quotient1_rec (cell f @ cell g).
    Proof.
      intros.
      refine (quotient1_ind_cell _ _ _ _ (g o f) @ _).
      refine (C_compose' f g @ _).
      refine (1 @@ _).
      refine (1 @@ ap _ (quotient1_ind_cell _ _ _ _ f)^ @@ (quotient1_ind_cell _ _ _ _ g)^ @ _).
      refine (apD_pp _ _ _)^.
    Defined.

      
    Lemma quotient1_rec_compose : forall {x y z} (f : R x y) (g : R y z),
        apD02 quotient1_rec (cell_compose f g) = quotient1_rec_compose'' f g.
    Proof.
      intros.
      apply quotient1_ind_compose.
    Qed.

  
  End quotient1_rec.

  Section quotient1_rec_set.

    Variable C : Type.
    Variable C_point : A -> C.
    Variable C_cell : forall {x y}, R x y -> C_point x = C_point y.
    Context {C_set : IsHSet C}.

    Definition quotient1_rec_set : quotient1 -> C.
    Proof.
      apply quotient1_rec with (C_point := C_point) (C_cell := C_cell);
      intros.
      - apply C_set.
      - apply trunc_succ.
    Defined.
  End quotient1_rec_set.

  Section quotient1_ind_set.
    
    Variable P : quotient1 -> Type.
    Context {P_set : forall a, IsHSet (P a)}.
    Variable P_point : forall x, P (point x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.

    Definition quotient1_ind_set : forall (q : quotient1), P q.
    Proof.
      apply quotient1_ind with (P_point := P_point) (P_cell := P_cell); intros.
      - apply trunc_succ.
      - apply P_set.
    Defined.
  End quotient1_ind_set.



End Domain.
End Quotient1.