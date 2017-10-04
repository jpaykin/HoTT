(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics.
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

  Private Inductive quotient1 (R : A -> A -> Type) 
                    `{IsHSet A} `{R_HSet : forall x y, IsHSet (R x y)}
                    `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R} 
                     (G : groupoid A R) : Type :=
  | point : A -> quotient1 R G
  .
  Axiom cell : forall {x y}, R x y -> point R G x = point R G y.
  Axiom cell_compose : forall {x y z} (f : R x y) (g : R y z),
        cell (g o f)%groupoid = cell f @ cell g.
  Axiom quotient1_trunc : IsTrunc 1 (quotient1 R G).
  Global Existing Instance quotient1_trunc.

  Section quotient1_ind.

    Variable P : quotient1 R G -> Type.
    Context {P_1Type : forall a, IsTrunc 1 (P a)}.
    Variable P_point : forall x, P (point R G x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.
    Variable P_compose : forall x y z (f : R x y) (g : R y z),
             P_cell _ _ (g o f)
           = transport2 P (cell_compose f g) (P_point x)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell _ _ f)
           @ P_cell _ _ g).

    Definition quotient1_ind (a : quotient1 R G) : P a :=
      ( match a with
        | point x => fun _ _ _ => P_point x
        end ) P_1Type P_cell P_compose.
    Axiom quotient1_ind_cell : forall {x y} (f : R x y),
          apD quotient1_ind (cell f) = P_cell _ _ f.

    Let quotient1_ind_compose' : forall {x y z} (f : R x y) (g : R y z),
        apD quotient1_ind (cell (g o f))
      = transport2 P (cell_compose f g) (quotient1_ind (point R G x))
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


    Definition quotient1_rec : quotient1 R G -> C.
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
      = transport2 (fun _ => C) (cell_compose f g) (quotient1_rec (point R G x))
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

    Definition quotient1_rec_set : quotient1 R G -> C.
    Proof.
      apply quotient1_rec with (C_point := C_point) (C_cell := C_cell);
      intros.
      - apply C_set.
      - apply trunc_succ.
    Defined.
  End quotient1_rec_set.

  Section quotient1_ind_set.
    
    Variable P : quotient1 R G -> Type.
    Context {P_set : forall a, IsHSet (P a)}.
    Variable P_point : forall x, P (point R G x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.

    Definition quotient1_ind_set : forall (q : quotient1 R G), P q.
    Proof.
      apply quotient1_ind with (P_point := P_point) (P_cell := P_cell); intros.
      - apply trunc_succ.
      - apply P_set.
    Defined.
  End quotient1_ind_set.

  Section quotient1_ind2.
    Variable P : quotient1 R G -> quotient1 R G -> Type.
    Context {P_1Type : forall q r, IsTrunc 1 (P q r)}.
    Variable P_point : forall x y, P (point R G x) (point R G y).


    Let P_HSet : forall {q r} (pf1 pf2 : P q r), IsHSet (pf1 = pf2).
    Proof.
      intros.
      intros x y. simpl.
      apply P_1Type.
    Qed.


    Variable P_cell_l : forall {x x' y} (f : R x x'),
                        transport (fun r => P r (point R G y)) (cell f) (P_point x y) 
                      = P_point x' y.

    Variable P_compose_l : forall {x1 x2 x3 y} (f : R x1 x2) (g : R x2 x3),
             P_cell_l _ _ y (g o f)
           = transport2 _ (cell_compose f g) (P_point x1 y)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell_l _ _ y f)
           @ P_cell_l _ _ y g).


    Variable P_cell_r : forall x {y y'} (f : R y y'),
                        transport (P (point R G x)) (cell f) (P_point x y) 
                      = P_point x y'.

    Variable P_compose_r : forall {x y1 y2 y3} (f : R y1 y2) (g : R y2 y3),
             P_cell_r x _ _ (g o f)
           = transport2 _ (cell_compose f g) (P_point x y1)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell_r x _ _ f)
           @ P_cell_r x _ _ g).



    Let P_point' (q : quotient1 R G) : forall y, P q (point R G y).
    Proof.
      intros y.
      generalize dependent q. 
      set (Q := fun r => P r (point R G y)).
      transparent assert (P_point0 : (forall x, P (point R G x) (point R G y))).
      { intros x. exact (P_point x y). }
      transparent assert (P_cell0 : (forall {x x'} (f : R x x'),
                 transport Q (cell f) (P_point0 x) = P_point0 x')).
      { intros x x' f. unfold Q, P_point0.
        apply P_cell_l.
      }
      apply quotient1_ind with (P_point := P_point0) (P_cell := P_cell0);
        unfold Q; auto.
      intros x1 x2 x3 f g.
      unfold P_cell0.
      apply P_compose_l.
    Defined.

    Variable P_cell_r_eq : forall {x x' y y'} (f : R x x') (g : R y y'),
        transport (fun r => transport (P r) (cell g) (P_point' r y) = P_point' r y')
                  (cell f) (P_cell_r x y y' g) 
      = P_cell_r x' y y' g.


    Let P_cell_r' q : forall {y y'} (g : R y y'),
                      transport (P q) (cell g) (P_point' q y)
                    = P_point' q y'.
    Proof.
      intros.
      generalize dependent q.
      set (Q := fun r => transport (P r) (cell g) (P_point' r y) = P_point' r y').
      transparent assert (Q_point : (forall x, Q (point R G x))).
      { intros; unfold Q. simpl.
        apply P_cell_r.
      }
      apply quotient1_ind_set with (P_point := Q_point).
      - unfold Q. intros. apply P_HSet.
      - intros. apply P_cell_r_eq.
    Defined.

    Let P_cell' : forall (q : quotient1 R G) {x' y'} (f : R x' y'),
                  cell f # P_point' q x' = P_point' q y'.
    Proof.
      intros.
      generalize dependent q.
      set (P0 := fun r => transport (P r) (cell f) (P_point' r x') = P_point' r y').
      transparent assert (P_point0 : (forall x, P0 (point R G x))).
      { intros x. apply P_cell_r. }
      apply quotient1_ind_set with (P_point := P_point0); intros; unfold P0; auto.
      unfold P_point0.
      apply P_cell_r_eq.
    Defined.


    Let Q {x y z} (f : R x y) (g : R y z) q := 
                    P_cell' q (g o f)
                   = transport2 (P q) (cell_compose f g) (P_point' q x)
                   @ ((transport_pp (P q) (cell f) (cell g) (P_point' q x)
                   @ ap (transport (P q) (cell g)) (P_cell' q f))
                   @ P_cell' q g).

    Let Q_point : forall {y1 y2 y3} (f : R y1 y2) (g : R y2 y3) x,
                  Q f g (point R G x).
    Proof.
      intros; unfold Q.
      simpl.
      apply P_compose_r.
    Defined.

    Let P_compose' : forall {x y z} (f : R x y) (g : R y z) q,
                     Q f g q.
    Proof.
      intros.
      generalize dependent q.
      apply quotient1_ind_set with (P_point := Q_point f g); intros.
      - apply trunc_succ.
      - unfold Q_point.
        set (X := P_compose_r y0 x y z f g).
        set (H := P_HSet _ _ (P_cell_r y0 x z (g o f))).
        simpl in H.
        apply H.
    Defined.

    Definition quotient1_ind2 : forall q r, P q r.
    Proof.
      intros q.
      apply quotient1_ind with (P_point := P_point' q) (P_cell := @P_cell' q);
        intros; auto.
      apply P_compose'.
    Defined.
  End quotient1_ind2.

  Section quotient1_rec2.

    Variable C : Type.
    Context {C_1Type : IsTrunc 1 C}.
    Variable C_point : A -> A -> C. About quotient1_rec.
    Variable C_cell : forall {x x' y y'} (f : R x x') (g : R y y'),
             C_point x y = C_point x' y'.
    Variable C_compose : forall {x1 x2 x3 y1 y2 y3} 
                                (f1 : R x1 x2) (f2 : R x2 x3) (g1 : R y1 y2) (g2 : R y2 y3),
             C_cell _ _ _ _ (f2 o f1) (g2 o g1)
           = C_cell _ _ _ _ f1 g1 @ C_cell _ _ _ _ f2 g2.


    Let C_HSet : forall (pf1 pf2 : C), IsHSet (pf1 = pf2).
    Proof.
      intros.
      intros x y. simpl.
      apply C_1Type.
    Qed.


    Definition C_point2_l : quotient1 R G -> A -> C.
    Proof.
      intros q x. generalize dependent q. About quotient1_rec.
      transparent assert (C_cell' : (forall y1 y2, R y1 y2 ->
        C_point x y1 = C_point x y2)).
      { intros y1 y2 g. apply (C_cell _ _ _ _ 1%groupoid g). }
      apply quotient1_rec with (C_point := fun y => C_point x y)
                               (C_cell := C_cell'); auto.
      intros.
      unfold C_cell'.
      refine (_ @ C_compose _ _ _ _ _ _ _ _ _ _).
      refine (ap (fun r => C_cell _ _ _ _ r (g o f)) _).
      apply (g_1_l G 1)^.
    Defined.


  Variable C_cell_r_eq : forall {x1 x2 y1 y2} (f : R x1 x2) (g : R y1 y2),
           transport (fun q => C_point2_l q y1 = C_point2_l q y2)
                     (cell f) (C_cell y1 y2 x1 x1 g 1) = C_cell y1 y2 x2 x2 g 1.
(*

  Variable C_cell_l_eq : forall {x1 x2 y1 y2} (f : R x1 x2) (g : R y1 y2),
           transport (fun q => C_point' q y1 = C_point' q y2)
                     (cell g) (C_cell y1 y1 _ _ 1 f) = C_cell y2 y2 _ _ 1 f.
*)


    Let C_cell' : forall q {y1 y2} (g : R y1 y2), C_point2_l q y1 = C_point2_l q y2.
    Proof.
      intros.
      generalize dependent q.
      transparent assert (P_point : (forall x, C_point2_l (point R G x) y1 = C_point2_l (point R G x) y2)).
      { unfold C_point2_l; intros. simpl.
        apply (C_cell _ _ _ x g 1%groupoid).
      }
      apply quotient1_ind_set with (P_point := P_point); intros.
      - apply C_HSet.
      - unfold P_point.
        apply C_cell_r_eq.
    Defined.


    Let C_compose' : forall q {y1 y2 y3} (f : R y1 y2) (g : R y2 y3),
        C_cell' q (g o f) = C_cell' q f @ C_cell' q g.        
    Proof.
      intros.
      generalize dependent q.
      set (Q := fun q => C_cell' q (g o f) = C_cell' q f @ C_cell' q g).
      About quotient1_ind_set.
      transparent assert (Q_point : (forall x, Q (point R G x))).
      { intros. unfold Q.
        simpl.
        About C_compose. 
        refine (_ @ (C_compose _ _ _ _ _ _ _ _ _ _)).
        refine (ap (fun r => C_cell _ _ _ _ (g o f) r) _).
        apply (g_1_l G _)^.
      }
      apply quotient1_ind_set with (P_point := Q_point); intros; auto.
      - apply trunc_succ.
      - apply C_HSet.
    Defined.


    Definition quotient1_rec2 : quotient1 R G -> quotient1 R G -> C.
    Proof.
      intros q.
      apply quotient1_rec with (C_point := C_point2_l q) (C_cell := @C_cell' q).
      - apply C_compose'.
      - auto.
    Defined.


  End quotient1_rec2.


End Domain.

Arguments quotient1 {A} {R} {IsHSet} {R_HSet} {reflR transR symmR} G : rename.
Arguments point {A} {R} {IsHSet} {R_HSet} {reflR transR symmR} G : rename.
Arguments cell {A} {R} {IsHSet} {R_HSet} {reflR transR symmR} G {x y} : rename.
Arguments cell_compose {A} {R} {IsHSet} {R_HSet} {reflR transR symmR} G {x y z} : rename.
About quotient1_rec2.
Arguments quotient1_ind {A R A_set R_HSet R_refl R_trans R_symm G} P {P_1Type}.
Arguments quotient1_rec {A R A_set R_HSet R_refl R_trans R_symm G}.
Arguments quotient1_ind_set {A R A_set R_HSet R_refl R_trans R_symm G} P {P_set}.
Arguments quotient1_rec_set {A R A_set R_HSet R_refl R_trans R_symm G}.
Arguments quotient1_ind2 {A R A_set R_HSet R_refl R_trans R_symm G} P {P_1Type}.
Arguments quotient1_rec2 {A R A_set R_HSet R_refl R_trans R_symm G}.

End Quotient1.