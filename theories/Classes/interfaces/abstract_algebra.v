Require Coq.Init.Peano.
Require Export
  HoTT.Classes.interfaces.canonical_names.

(* 
For various structures we omit declaration of substructures. For example, if we 
say:

Class Setoid_Morphism :=
  { setoidmor_a :> Setoid A
  ; setoidmor_b :> Setoid B
  ; sm_proper :> Proper ((=) ==> (=)) f }.

then each time a Setoid instance is required, Coq will try to prove that a
Setoid_Morphism exists. This obviously results in an enormous blow-up of the
search space. Moreover, one should be careful to declare a Setoid_Morphisms
as a substructure. Consider [f t1 t2], now if we want to perform setoid rewriting
in [t2] Coq will first attempt to prove that [f t1] is Proper, for which it will 
attempt to prove [Setoid_Morphism (f t1)]. If many structures declare
Setoid_Morphism as a substructure, setoid rewriting will become horribly slow.
*)

(* An unbundled variant of the former CoRN CSetoid. We do not 
  include a proof that A is a Setoid because it can be derived. *)
Class IsApart A {Aap : Apart A} : Type :=
  { apart_set :> IsHSet A
  ; apart_mere :> is_mere_relation _ apart
  ; apart_symmetric :> Symmetric (≶)
  ; apart_cotrans :> CoTransitive (≶)
  ; tight_apart : forall x y, ~x ≶ y <-> x = y }.

Instance apart_irrefl `{IsApart A} : Irreflexive (≶).
Proof.
intros x ap.
apply (tight_apart x x).
- reflexivity.
- assumption.
Qed.

Arguments tight_apart {A Aap IsApart} _ _.

Section setoid_morphisms.
  Context {A B} {Aap : Apart A} {Bap : Apart B} (f : A -> B).

  Class StrongExtensionality := strong_extensionality : forall x y, f x ≶ f y -> x ≶ y.
End setoid_morphisms.

(* HOTT TODO check if this is ok/useful *)
Hint Extern 4 (?f _ = ?f _) => eapply (ap f).

Section setoid_binary_morphisms.
  Context {A B C} {Aap: Apart A} 
    {Bap : Apart B} {Cap : Apart C} (f : A -> B -> C).

  Class StrongBinaryExtensionality := strong_binary_extensionality
    : forall x₁ y₁ x₂ y₂, f x₁ y₁ ≶ f x₂ y₂ -> hor (x₁ ≶ x₂) (y₁ ≶ y₂).
End setoid_binary_morphisms.

(*
Since apartness usually only becomes relevant when considering fields (e.g. the 
real numbers), we do not include it in the lower part of the algebraic hierarchy
(as opposed to CoRN).
*)
Section upper_classes.
  Universe i.
  Context (A : Type@{i}).

  Class SemiGroup {Aop: SgOp A} :=
    { sg_set :> IsHSet A
    ; sg_ass :> Associative (&) }.

  Class CommutativeSemiGroup {Aop : SgOp A} :=
    { comsg_sg :> @SemiGroup Aop
    ; comsg_comm :> Commutative (&) }.

  Class SemiLattice {Aop : SgOp A} :=
    { semilattice_sg :> @CommutativeSemiGroup Aop
    ; semilattice_idempotent :> BinaryIdempotent (&)}.

  Class Monoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { monoid_semigroup :> SemiGroup
    ; monoid_left_id :> LeftIdentity (&) mon_unit
    ; monoid_right_id :> RightIdentity (&) mon_unit }.

  Class CommutativeMonoid {Aop Aunit} :=
    { commonoid_mon :> @Monoid Aop Aunit
    ; commonoid_commutative :> Commutative (&) }.

  Class Group {Aop Aunit} {Anegate : Negate A} :=
    { group_monoid :> @Monoid Aop Aunit
    ; negate_l :> LeftInverse (&) (-) mon_unit
    ; negate_r :> RightInverse (&) (-) mon_unit }.

  Class BoundedSemiLattice {Aop Aunit} :=
    { bounded_semilattice_mon :> @CommutativeMonoid Aop Aunit
    ; bounded_semilattice_idempotent :> BinaryIdempotent (&)}.

  Class AbGroup {Aop Aunit Anegate} :=
    { abgroup_group :> @Group Aop Aunit Anegate
    ; abgroup_commutative :> Commutative (&) }.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class SemiRing :=
    { semiplus_monoid :> @CommutativeMonoid plus_is_sg_op zero_is_mon_unit
    ; semimult_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; semiring_distr :> LeftDistribute (.*.) (+)
    ; semiring_left_absorb :> LeftAbsorb (.*.) 0 }.

  Context {Anegate : Negate A}.

  Class Ring :=
    { ring_group :> @AbGroup plus_is_sg_op zero_is_mon_unit _
    ; ring_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; ring_dist :> LeftDistribute (.*.) (+) }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain :=
    { intdom_ring : Ring
    ; intdom_nontrivial : PropHolds (not (1 = 0))
    ; intdom_nozeroes :> NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/)
    because it can de derived *)
  Class Field {Aap: Apart A} {Arecip: Recip A} :=
    { field_ring :> Ring
    ; field_apart :> IsApart A
    ; field_plus_ext :> StrongBinaryExtensionality (+)
    ; field_mult_ext :> StrongBinaryExtensionality (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_inverse : forall x, x.1 // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/),
    f (/x) = / (f x), / /x = x, /x * /y = /(x * y) 
    hold without any additional assumptions *)
  Class DecField {Adec_recip : DecRecip A} :=
    { decfield_ring :> Ring
    ; decfield_nontrivial : PropHolds (1 <> 0)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : forall x, x <> 0 -> x / x = 1 }.

  Class FieldCharacteristic@{j} {Aap : Apart@{i j} A} (k : nat) : Type@{j}
    := field_characteristic : forall n : nat, Peano.lt 0 n ->
      iff@{j j j} (forall m : nat, not@{j j} (paths@{Set} n (Peano.mult k m)))
        (@apart A Aap (Peano.nat_iter n (1 +) 0) 0).

End upper_classes.

(* Due to bug #2528 *)
Hint Extern 4 (PropHolds (1 <> 0)) =>
  eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≶ 0)) =>
  eapply @field_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 <> 0)) =>
  eapply @decfield_nontrivial : typeclass_instances.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Arguments recip_inverse {A Aplus Amult Azero Aone Anegate Aap Arecip Field} _.
Arguments dec_recip_inverse
  {A Aplus Amult Azero Aone Anegate Adec_recip DecField} _ _.
Arguments dec_recip_0 {A Aplus Amult Azero Aone Anegate Adec_recip DecField}.

Section lattice.
  Context A {Ajoin: Join A} {Ameet: Meet A} {Abottom : Bottom A} {Atop : Top A}.

  Class JoinSemiLattice := 
    join_semilattice :> @SemiLattice A join_is_sg_op.
  Class BoundedJoinSemiLattice := 
    bounded_join_semilattice :> @BoundedSemiLattice A
      join_is_sg_op bottom_is_mon_unit.
  Class MeetSemiLattice := 
    meet_semilattice :> @SemiLattice A meet_is_sg_op.
  Class BoundedMeetSemiLattice :=
    bounded_meet_semilattice :> @BoundedSemiLattice A
      meet_is_sg_op top_is_mon_unit.

  Class Lattice := 
    { lattice_join :> JoinSemiLattice
    ; lattice_meet :> MeetSemiLattice
    ; join_meet_absorption :> Absorption (⊔) (⊓) 
    ; meet_join_absorption :> Absorption (⊓) (⊔)}.

  Class BoundedLattice :=
    { boundedlattice_join :> BoundedJoinSemiLattice
    ; boundedlattice_meet :> BoundedMeetSemiLattice
    ; boundedjoin_meet_absorption :> Absorption (⊔) (⊓)
    ; boundedmeet_join_absorption :> Absorption (⊓) (⊔)}.

  Class DistributiveLattice := 
    { distr_lattice_lattice :> Lattice
    ; join_meet_distr_l :> LeftDistribute (⊔) (⊓) }.
End lattice.

Section morphism_classes.

  Section sgmorphism_classes.
  Context {A B : Type} {Aop : SgOp A} {Bop : SgOp B}
    {Aunit : MonUnit A} {Bunit : MonUnit B}.

  Class SemiGroupPreserving (f : A -> B) :=
    preserves_sg_op : forall x y, f (x & y) = f x & f y.

  Class UnitPreserving (f : A -> B) :=
    preserves_mon_unit : f mon_unit = mon_unit.

  Class MonoidPreserving (f : A -> B) :=
    { monmor_sgmor :> SemiGroupPreserving f
    ; monmor_unitmor :> UnitPreserving f }.
  End sgmorphism_classes.

  Section ringmorphism_classes.
  Context {A B : Type} {Aplus : Plus A} {Bplus : Plus B}
    {Amult : Mult A} {Bmult : Mult B} {Azero : Zero A} {Bzero : Zero B}
    {Aone : One A} {Bone : One B}.

  Class SemiRingPreserving (f : A -> B) :=
    { semiringmor_plus_mor :> @MonoidPreserving A B
        plus_is_sg_op plus_is_sg_op zero_is_mon_unit zero_is_mon_unit f
    ; semiringmor_mult_mor :> @MonoidPreserving A B
        mult_is_sg_op mult_is_sg_op one_is_mon_unit one_is_mon_unit f }.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class SemiRingStrongPreserving (f : A -> B) :=
    { strong_semiringmor_sr_mor :> SemiRingPreserving f
    ; strong_semiringmor_strong_mor :> StrongExtensionality f }.
  End ringmorphism_classes.

  Section latticemorphism_classes.
  Context {A B : Type} {Ajoin : Join A} {Bjoin : Join B}
    {Ameet : Meet A} {Bmeet : Meet B}.

  Class JoinPreserving (f : A -> B) :=
    join_slmor_sgmor :> @SemiGroupPreserving A B join_is_sg_op join_is_sg_op f.

  Class MeetPreserving (f : A -> B) :=
    meet_slmor_sgmor :> @SemiGroupPreserving A B meet_is_sg_op meet_is_sg_op f.

  Context {Abottom : Bottom A} {Bbottom : Bottom B}.
  Class BoundedJoinPreserving (f : A -> B) := bounded_join_slmor_monmor
      :> @MonoidPreserving A B join_is_sg_op join_is_sg_op
         bottom_is_mon_unit bottom_is_mon_unit f.

  Class LatticePreserving (f : A -> B) :=
    { latticemor_join_mor :> JoinPreserving f
    ; latticemor_meet_mor :> MeetPreserving f }.
  End latticemorphism_classes.
End morphism_classes.

Section jections.
  Context {A B} (f : A -> B).

  Class Injective := injective : forall x y, f x = f y -> x = y.

  Lemma injective_ne `{!Injective} x y :
    x <> y -> f x <> f y.
  Proof.
    intros E1 E2. apply E1.
    apply injective.
    assumption.
  Qed.
End jections.

Section strong_injective.
  Context {A B} {Aap : Apart A} {Bap : Apart B} (f : A -> B) .
  Class StrongInjective :=
    { strong_injective : forall x y, x ≶ y -> f x ≶ f y
    ; strong_injective_mor : StrongExtensionality f }.
End strong_injective.

Section extras.

Class CutMinusSpec A (cm : CutMinus A) `{Zero A} `{Plus A} `{Le A} := {
  cut_minus_le : forall x y, y ≤ x -> x ∸ y + y = x ;
  cut_minus_0 : forall x y, x ≤ y -> x ∸ y = 0
}.

End extras.
