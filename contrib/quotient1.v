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
(*Arguments quotient1_rec2 {A R A_set R_HSet R_refl R_trans R_symm G}.*)

End Quotient1.


(******************************)

  Open Scope groupoid_scope.

  Section quotient1_map.

    Variable A : Type.
    Variable R_A : A -> A -> Type.
    Context {A_set : IsHSet A} 
            {R_A_HSet : forall x y, IsHSet (R_A x y)}
            {R_A_refl : Reflexive R_A}
            {R_A_trans : Transitive R_A}
            {R_A_symm : Symmetric R_A}.
    Variable G_A : groupoid A R_A.

    Variable B : Type.
    Variable R_B : B -> B -> Type.
    Context {B_set : IsHSet B} 
            {R_B_HSet : forall x y, IsHSet (R_B x y)}
            {R_B_refl : Reflexive R_B}
            {R_B_trans : Transitive R_B}
            {R_B_symm : Symmetric R_B}.
    Variable G_B : groupoid B R_B.

    Variable f : A -> B.
    (* Want: quotient f G_A G_B : (A/G_A) (B/G_B) *)



    Variable map_cell : forall {x y}, R_A x y -> R_B (f x) (f y).
    Variable map_1 : forall x, map_cell x x 1 = 1.
    Variable map_compose : forall {x y z} (f : R_A x y) (g : R_A y z),
             map_cell x z (g o f) = map_cell _ _ g o map_cell _ _ f.


    Definition quotient1_map : quotient1 G_A -> quotient1 G_B.
    Proof. 
      apply quotient1_rec 
        with (C_point := fun a => point G_B (f a)) 
             (C_cell := fun x y pf => cell G_B (map_cell _ _ pf)).
      * intros. 
        simpl.
        fold (g o f0).
        rewrite map_compose.

        rewrite cell_compose.
        reflexivity.
      * apply quotient1_trunc. 
    Defined.

  End quotient1_map.


    (* These should be derived from the library... *)
    Instance pair_HSet A B `{IsHSet A} `{IsHSet B} : IsHSet (A*B).
    Admitted.
    Instance R_pair_HSet {A B} (R_A : A -> A -> Type) (R_B : B -> B -> Type)
                              `{forall x y, IsHSet (R_A x y)} 
                              `{forall x y, IsHSet (R_B x y)} 
             : forall x y, IsHSet (R_pair R_A R_B x y).
    Proof.
      intros [a b] [a' b'].
      unfold R_pair.
      apply pair_HSet; auto.
    Qed.

  Section quotient1_curry.

    Variable A : Type.
    Variable R_A : A -> A -> Type.
    Context {A_set : IsHSet A} 
            {R_A_HSet : forall x y, IsHSet (R_A x y)}
            {R_A_refl : Reflexive R_A}
            {R_A_trans : Transitive R_A}
            {R_A_symm : Symmetric R_A}.
    Variable G_A : groupoid A R_A.

    Variable B : Type.
    Variable R_B : B -> B -> Type.
    Context {B_set : IsHSet B} 
            {R_B_HSet : forall x y, IsHSet (R_B x y)}
            {R_B_refl : Reflexive R_B}
            {R_B_trans : Transitive R_B}
            {R_B_symm : Symmetric R_B}.
    Variable G_B : groupoid B R_B.

    Let C_point_a_b (a : A) (b : B) : quotient1 (g_pair G_A G_B) := 
      point (g_pair G_A G_B) (a,b).
    Let C_cell_a_b (b : B) : forall a a', R_A a a' ->
          point (g_pair G_A G_B) (a,b) = point (g_pair G_A G_B) (a',b).
    Proof.
      intros a a' f.
      apply cell.
      split; [exact f | exact 1].
    Defined.

    Let C_cell_b b : forall x y z (f : R_A x y) (g : R_A y z),
        C_cell_a_b b x z (g o f) = C_cell_a_b b x y f @ C_cell_a_b b y z g.
    Proof.
      intros x y z f g.
      unfold C_cell_a_b. 
      set (k := (g o f, 1) : R_pair R_A R_B (x,b) (z,b)).
      set (k2 := (g,1) : R_pair R_A R_B (y,b) (z,b)).
      set (k1 := (f,1) : R_pair R_A R_B (x,b) (y,b)).
      assert (pf : k = k2 o k1). 
      { unfold k, k1, k2.
        simpl.
        unfold R_trans.
        fold (1 : R_B b b).
        fold (1 o 1 : R_B b b).
        rewrite (g_1_l G_B).
        reflexivity.
      }
      rewrite pf.
      apply cell_compose.
    Qed.


    Let C_point_b : quotient1 G_A -> B -> quotient1 (g_pair G_A G_B).
    Proof.
      intros q_a b.
      generalize dependent q_a.
      apply quotient1_rec 
        with (C_point := fun a => point (g_pair G_A G_B) (a,b))
             (C_cell := C_cell_a_b b);
        [ | apply quotient1_trunc].
      apply (C_cell_b b).
    Defined.

    Let P0 {x y} (f : R_B x y) (q_a : quotient1 G_A) : Type := 
                                   C_point_b q_a x = C_point_b q_a y.
    Let P_point0 {x y} (f : R_B x y) : forall a, P0 f (point G_A a).
    Proof.
      intros. 
      unfold P0. simpl.
      apply cell.
      split; [exact 1 | exact f].
    Defined.

    (* Don't know how to prove this.. *)
    Let P_cell0 {b b'} (f : R_B b b') : forall a a' (g : R_A a a'),
        transport (P0 f) (cell _ g) (P_point0 f a) = (P_point0 f a').
    Proof.
      intros a a' g.
      unfold P_point0.
      unfold P0.
      Search (transport _ _ (cell _ _)).
      About apD.
    Admitted.    

    Let C_cell_curry q_a : forall x y, R_B x y -> C_point_b q_a x = C_point_b q_a y.
    Proof.
      intros x y f .
      generalize dependent q_a.
      apply quotient1_ind with (P := P0 f)
                               (P_point := P_point0 f)
                               (P_cell := P_cell0 f).
      * intros q_a. unfold P0. 
        apply trunc_succ.
      * intros. apply quotient1_trunc.
    Defined.

    Let C_compose_curry q_a : forall x y z (f : R_B x y) (g : R_B y z),
        C_cell_curry q_a x z (g o f) 
      = C_cell_curry q_a x y f @ C_cell_curry q_a y z g.
    Proof.
      intros.
      generalize dependent q_a.

      set (P1 q_a := 
        C_cell_curry q_a x z (g o f) 
      = C_cell_curry q_a x y f @ C_cell_curry q_a y z g).
      
      assert (P_point1 : forall a, P1 (point _ a)).
      { intros. unfold P1. simpl.
        fold (g o f). 
        unfold P_point0.
        admit (* this is true *).
      }


      apply quotient1_ind_set with (P := P1)
                                   (P_point := P_point1).
      * intros q_a. apply trunc_succ.
      * intros. apply quotient1_trunc.
    Admitted.



    Definition quotient1_curry 
             : quotient1 G_A -> quotient1 G_B -> quotient1 (g_pair G_A G_B).
    Proof.
      intros q_a.
      apply quotient1_rec 
        with (C_point := C_point_b q_a)
             (C_cell := C_cell_curry q_a);
      [ apply C_compose_curry | apply quotient1_trunc].
    Defined.


  End quotient1_curry.

  Section quotient1_rec2.

    Variable A : Type.
    Variable R_A : A -> A -> Type.
    Context {A_set : IsHSet A} 
            {R_A_HSet : forall x y, IsHSet (R_A x y)}
            {R_A_refl : Reflexive R_A}
            {R_A_trans : Transitive R_A}
            {R_A_symm : Symmetric R_A}.
    Variable G_A : groupoid A R_A.

    Variable B : Type.
    Variable R_B : B -> B -> Type.
    Context {B_set : IsHSet B} 
            {R_B_HSet : forall x y, IsHSet (R_B x y)}
            {R_B_refl : Reflexive R_B}
            {R_B_trans : Transitive R_B}
            {R_B_symm : Symmetric R_B}.
    Variable G_B : groupoid B R_B.

    Variable C : Type.
    Context {C_1Type : IsTrunc 1 C}.
    Variable C_point : A -> B -> C. 
    Variable C_cell : forall {x x' y y'} (f : R_A x x') (g : R_B y y'),
             C_point x y = C_point x' y'.

    Variable C_compose : forall {x1 x2 x3 y1 y2 y3} 
                                (f1 : R_A x1 x2) (f2 : R_A x2 x3) 
                                (g1 : R_B y1 y2) (g2 : R_B y2 y3),
             C_cell _ _ _ _ (f2 o f1) (g2 o g1)
           = C_cell _ _ _ _ f1 g1 @ C_cell _ _ _ _ f2 g2.


    Let C_HSet : forall (pf1 pf2 : C), IsHSet (pf1 = pf2).
    Proof.
      intros.
      intros x y. simpl.
      apply C_1Type.
    Qed.


    Let C_point' (z : A * B) : C :=
      let (a,b) := z in C_point a b.
    Let C_cell' (z z' : A*B) : R_pair R_A R_B z z' -> C_point' z = C_point' z'.
    Proof.
      destruct z as [a b], z' as [a' b'].
      intros [pf_a pf_b]; simpl in *.
      unfold C_point'.
      apply (C_cell _ _ _ _ pf_a pf_b).
    Defined.

    Let quotient1_rec2_curry : quotient1 (g_pair G_A G_B) -> C.
    Proof.
      apply quotient1_rec 
        with (C_point0 := C_point')
             (C_cell0 := C_cell'); auto.
      intros [a1 b1] [a2 b2] [a3 b3] [a12 b12] [a13 b13].
      unfold C_cell'. simpl.
      fold (a13 o a12).
      fold (b13 o b12).
      apply C_compose.
    Qed.

    Definition quotient1_rec2 : quotient1 G_A -> quotient1 G_B -> C.
    Proof.
      intros a b.
      apply quotient1_rec2_curry.
      apply (quotient1_curry _ _ _ _ _ _ a b).
    Defined.
  End quotient1_rec2.




  Section quotient1_map2.


    Variable A : Type.
    Variable R_A : A -> A -> Type.
    Context {A_set : IsHSet A} 
            {R_A_HSet : forall x y, IsHSet (R_A x y)}
            {R_A_refl : Reflexive R_A}
            {R_A_trans : Transitive R_A}
            {R_A_symm : Symmetric R_A}.
    Variable G_A : groupoid A R_A.

    Variable B : Type.
    Variable R_B : B -> B -> Type.
    Context {B_set : IsHSet B} 
            {R_B_HSet : forall x y, IsHSet (R_B x y)}
            {R_B_refl : Reflexive R_B}
            {R_B_trans : Transitive R_B}
            {R_B_symm : Symmetric R_B}.
    Variable G_B : groupoid B R_B.

    Variable C : Type.
    Variable R_C : C -> C -> Type.
    Context {C_set : IsHSet C} 
            {R_C_HSet : forall x y, IsHSet (R_C x y)}
            {R_C_refl : Reflexive R_C}
            {R_C_trans : Transitive R_C}
            {R_C_symm : Symmetric R_C}.
    Variable G_C : groupoid C R_C.

    Variable f : A -> B -> C.
    (* Want: quotient G_A G_B G_C f : A/G_A -> B/G_B -> C/G_C *)
    Variable map_cell : forall {a a' b b'}, 
             R_A a a' -> R_B b b' -> R_C (f a b) (f a' b').
    Variable map_compose : forall {a1 a2 a3 b1 b2 b3}
                                  (a12 : R_A a1 a2) (a23 : R_A a2 a3)
                                  (b12 : R_B b1 b2) (b23 : R_B b2 b3),
        map_cell _ _ _ _ (a23 o a12) (b23 o b12) 
     = (map_cell _ _ _ _ a23 b23) o (map_cell _ _ _ _ a12 b12).

    Let C_point0 := fun a b => point G_C (f a b).
    Let C_cell0 : forall x x' y y', R_A x x' -> R_B y y' -> 
                  point G_C (f x y) = point G_C (f x' y').
    Proof.
      intros. apply cell. apply map_cell; auto.
    Defined.

    Let C_compose0 : forall (x1 x2 x3 : A) (y1 y2 y3 : B) (f1 : R_A x1 x2) 
                            (f2 : R_A x2 x3) (g1 : R_B y1 y2) (g2 : R_B y2 y3),
        C_cell0 x1 x3 y1 y3 (f2 o f1) (g2 o g1) =
        C_cell0 x1 x2 y1 y2 f1 g1 @ C_cell0 x2 x3 y2 y3 f2 g2.
    Proof.
      intros.
      unfold C_cell0.
      rewrite map_compose.
      apply cell_compose.
    Defined.
      
    Definition quotient1_map2 : quotient1 G_A -> quotient1 G_B -> quotient1 G_C.
    Proof.

      apply quotient1_rec2 with (C_point := C_point0)
                                (C_cell := C_cell0);
        [ apply quotient1_trunc | apply C_compose0 ].
    Defined.


  End quotient1_map2.



(*
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
*)