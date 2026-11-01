import Tltt.Reedy.ReedyFibrancy
import Misc.Category

noncomputable section
namespace Tltt.ReedyFibrancy
open CategoryTheory
open Fibrancy
open Hott

@[ext]
structure ReedyPresheaf (D : Type _) [DirectCategory D] (n : Nat) : Type _ where
  presheaf : Psh (Below D n)
  is_reedy : is_reedy_up_to n presheaf

namespace ReedyPresheaf
  def ext' {D : Type*} [DirectCategory D] {n : Nat} (F G : ReedyPresheaf D n)
           (p : F.presheaf = G.presheaf)
           (q : ∀ i, F.is_reedy i = eqToHom (C := Type _) (by rw [p]) (G.is_reedy i))
           : F = G := by
    induction F with | mk pshF is_reedy_F =>
    induction G with | mk pshG is_reedy_G =>
    dsimp only at p q
    induction p
    simp
    funext
    apply q
    
  def empty (D : Type _) [DirectCategory D] : ReedyPresheaf D 0 where
    presheaf := empty.functor D
    is_reedy := by
      intro i
      exfalso
      apply Nat.not_lt_zero
      exact i.rank_is_lt

  def psh_below_zero_eqv_unit {D : Type*} [DirectCategory D] : ReedyPresheaf D 0 ≃ PUnit where
    toFun _ :=
      .unit
    invFun _ :=
      empty D
    left_inv := by
      intro X
      simp
      ext
      · apply eq_of_empty_shape
        calc
          _ ≃ Below D 0 := op_eqv
          _ ≃ _ := Below.eqv_empty_of_zero
      · apply heq_of_cast_eq
        · funext x
          exfalso
          apply Nat.not_lt_zero
          apply x.rank_is_lt
        · apply piext
          intro x
          exfalso
          apply Nat.not_lt_zero
          apply x.rank_is_lt
    right_inv := by
      intro
      ext

end ReedyPresheaf

def fib_below_zero {D : Type*} [DirectCategory D] : IsFibrantWeak (ReedyPresheaf D 0) := by
  apply fibrant_of_eqv_fibrant (α := Unit)
  · apply unit_is_fibrant
  · apply Equiv.symm
    apply ReedyPresheaf.psh_below_zero_eqv_unit

universe u₁ u₂ in
@[ext]
structure LayeredReedyPresheaf (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat)
          extends Presheaf.LayeredPresheaf D n where
  is_reedy : is_reedy_up_to.{u₁, u₂} n X
  is_fibrant (i : OfRank D n) : is_reedy_at.{u₁, max u₁ u₂} i.point (restrict₄ i toLayeredPresheaf.to_psh)

namespace LayeredReedyPresheaf
  universe u₁ u₂
  variable {D : Type u₁} [DirectCategory.{u₁, max u₁ u₂} D] {n : Nat}
  
  section ToPsh
  variable (self : LayeredReedyPresheaf D n)

  variable (i : Below D (n+1))

  def to_rd_psh : ReedyPresheaf D (n+1) where
    presheaf := self.toLayeredPresheaf.to_psh
    is_reedy (i : Below D (n+1)) :=
      if h : rk i = n then
        let i' : OfRank D n := ⟨i.point, h⟩
        self.is_fibrant i'
      else by
        let i' : Below D n := i.of_succ_of_rk_ne h
        suffices h : restrict₂ i self.to_psh = restrict₂ i' self.X
        rw [h]
        apply self.is_reedy i'
        refine CategoryTheory.Functor.ext ?object ?map
        · intro j
          simp [restrict₂]
          apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n
          apply Nat.ne_of_lt
          simp
          calc
            _ ≤ rk i := by
              apply Nat.le_of_lt_succ
              apply Below.rank_is_lt
            _ = rk i' := rfl
            _ < n := i'.rank_is_lt
        · intro j k f
          apply ConcreteCategory.coe_ext
          apply Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n <;> simp <;> {
            apply Nat.ne_of_lt
            calc
            _ ≤ rk i := by
              apply Nat.le_of_lt_succ
              apply Below.rank_is_lt
            _ = rk i' := rfl
            _ < n := by apply Below.rank_is_lt
          }
  end ToPsh

  section OfPsh
  variable (F : ReedyPresheaf D (n+1))

  @[simp]
  def of_rd_psh : LayeredReedyPresheaf D n where
    toLayeredPresheaf := Presheaf.LayeredPresheaf.of_psh F.presheaf
    is_fibrant := by
      intro i
      let i' : Below D (n+1) := i.as_below
      rw [Presheaf.LayeredPresheaf.left_inv]
      suffices h : restrict₄ i F.presheaf = restrict₂ i' F.presheaf
      rw [h]
      apply F.is_reedy i'
      rfl
    is_reedy := by
      intro i
      let i' : Below D (n+1) := i.up
      simp [Presheaf.LayeredPresheaf.of_psh]
      suffices h : restrict₂ i (restrict₁ F.presheaf) = restrict₂ i' F.presheaf
      rw [h]
      apply F.is_reedy i'
      rfl
  end OfPsh

  private theorem eqToHom_apply_heq {α β : Type _} (h : α = β) (a : α) :
      HEq (eqToHom h a) a := by
    cases h
    rfl

  private theorem dite_heq {α β : Sort _} (p : Prop) [Decidable p]
      (t : p → α) (f : ¬p → α) (b : β)
      (ht : ∀ h, HEq (t h) b) (hf : ∀ h, HEq (f h) b) : HEq (dite p t f) b := by
    split
    · apply ht
    · apply hf

  @[simp]
  def left_inv : Function.LeftInverse (to_rd_psh (D := D) (n := n)) of_rd_psh := by
    intro ⟨psh, psh_is_reedy⟩
    apply ReedyPresheaf.ext' _ _ (Presheaf.LayeredPresheaf.left_inv psh)
    intro i
    apply eq_of_heq
    apply HEq.trans ?_ (eqToHom_apply_heq _ _).symm
    dsimp only [to_rd_psh]
    apply dite_heq
    · intro h
      dsimp [of_rd_psh]
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      rfl
    · intro h
      dsimp [of_rd_psh]
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      rfl

  def right_inv : Function.RightInverse (to_rd_psh (D := D) (n := n)) of_rd_psh := by
    intro l
    apply ext_heq _ _ (Presheaf.LayeredPresheaf.right_inv l.toLayeredPresheaf)
    · apply Function.hfunext rfl
      intro i j hij
      cases eq_of_heq hij
      dsimp [of_rd_psh]
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      dsimp [to_rd_psh]
      apply dite_heq
      · intro h
        exact False.elim ((Nat.ne_of_lt i.rank_is_lt) h)
      · intro h
        exact cast_heq _ _
    · apply Function.hfunext rfl
      intro i j hij
      cases eq_of_heq hij
      dsimp [of_rd_psh]
      apply HEq.trans (cast_heq _ _)
      apply HEq.trans (cast_heq _ _)
      dsimp [to_rd_psh]
      apply dite_heq
      · intro h
        rfl
      · intro h
        exact False.elim (h i.rank_is)
  where
    ext_heq (a b : LayeredReedyPresheaf D n)
        (h : a.toLayeredPresheaf = b.toLayeredPresheaf)
        (hr : HEq a.is_reedy b.is_reedy)
        (hf : HEq a.is_fibrant b.is_fibrant) : a = b := by
      cases a
      cases b
      cases h
      cases hr
      cases hf
      rfl

  def eqv_of_layer_below : ReedyPresheaf D (n+1) ≃ LayeredReedyPresheaf D n where
    toFun := of_rd_psh
    invFun := to_rd_psh
    left_inv := left_inv
    right_inv := right_inv
end LayeredReedyPresheaf

universe u₁ u₂ in
structure CompactLRP (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat) where
  X : ReedyPresheaf D n
  glueing : ∀ i : OfRank D n,
            MatchingObject i.point (restrict₅ i X.presheaf)
            → Typeₒ max u₁ u₂

universe u₁ u₂ in
abbrev SigmaCompactLRP (D : Type u₁) [DirectCategory.{u₁, max u₁ u₂} D] (n : Nat) :=
  Σ X : ReedyPresheaf D n,
  ∀ i : OfRank D n,
  MatchingObject i.point (restrict₅ i X.presheaf) → Typeₒ max u₁ u₂

namespace CompactLRP
  universe u₁ u₂
  variable {D : Type u₁} [DirectCategory.{u₁, max u₁ u₂} D] {n : Nat}

  namespace ToLRP
  variable (self : CompactLRP.{u₁, u₂} D n)

  abbrev X : Psh (Below D n) :=
    self.X.presheaf

  abbrev Y (i : OfRank D n) : Type _ :=
    Σ z, self.glueing i z

  abbrev u {i : OfRank D n} {j : Below D n} (f : j.point ⟶ i.point) : Y self i → (X self).obj (.op j) := by
    intro y
    induction y with | mk z a =>
    let cone := MatchingObject.limit_cone i.point (restrict₅ i self.X.presheaf) |>.cone
    have : i.point ≠ j.point := by
      intro i_eq_j
      apply Nat.lt_irrefl n
      conv =>
        lhs
        rw [← i.rank_is, i_eq_j]
      apply j.rank_is_lt
    induction i with | mk i rk_i_eq_n =>
    induction rk_i_eq_n
    have := cone.π.app ⟨j.point, f, this⟩
    dsimp [restrict₅, under.inclusion] at this
    exact this z

  abbrev is_reedy : is_reedy_up_to n (X self) :=
    self.X.is_reedy

  abbrev coh : ∀ {i : OfRank D n} {j k : Below D n} (f : j.point ⟶ i.point) (g : k ⟶ j),
               (X self).map g.op ∘ u self f = u self (g ≫ f) := by
    intro ⟨i, rk_i_eq_n⟩ j k f g
    induction rk_i_eq_n
    dsimp
    funext ⟨z, hello⟩
    simp
    let cone := (MatchingObject.limit_cone i self.X.presheaf).cone
    let j' : under i := by
      exists j.point, f
      intro i_eq_j
      apply Nat.lt_irrefl (rk i)
      conv =>
        lhs
        rw [i_eq_j]
      apply Below.rank_is_lt
    let k' : under i := by
      exists k.point, g ≫ f
      intro k_eq_j
      apply Nat.lt_irrefl (rk i)
      conv =>
        lhs
        rw [k_eq_j]
      apply Below.rank_is_lt
    let g' : k' ⟶ j' := by exists g
    apply Eq.symm
    exact ConcreteCategory.congr_hom (cone.π.naturality (.op g')) z

  abbrev layered_presheaf : Presheaf.LayeredPresheaf D n where
    X := X self
    Y := Y self
    u := u self
    coh := coh self

  theorem restrict_lp_to_psh : (restrict₁ (layered_presheaf self).to_psh) = self.X.presheaf := by
    refine CategoryTheory.Functor.ext ?object ?map
    · intro ⟨i⟩
      unfold Presheaf.LayeredPresheaf.to_psh
      simp
      rw [Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n]
      · simp [X]
        rfl
      · simp
        intro h
        apply Nat.lt_irrefl n
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
    · intro ⟨i⟩ ⟨j⟩ f
      simp [restrict₁, layered_presheaf, Presheaf.LayeredPresheaf.to_psh]
      rw [Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n]
      · rfl
      · exact Nat.ne_of_lt i.rank_is_lt
      · exact Nat.ne_of_lt j.rank_is_lt

  lemma sigma_transport {A B : Type u₁} (p : A = B) (E : B → Typeₒ u₂) :
      (Σ a : A, E (eqToHom p a)) = (Σ b : B, E b) := by
    cases p
    rfl

  lemma heq_casts {A B C D : Type u₁} (p : A = B) (q : C = D) (f : B → C) :
      HEq (eqToHom q ∘ f ∘ eqToHom p) f := by
    cases p
    cases q
    rfl

  lemma sigma_fst_transport {A B : Type u₁} (p : A = B) (E : B → Typeₒ u₂) :
      HEq (Sigma.fst : (Σ a : A, E (eqToHom p a)) → A)
        (Sigma.fst : (Σ b : B, E b) → B) := by
    cases p
    rfl

  lemma lift_heq {J : Type u₁} [Category J] {F G : J ⥤ Type u₁} (p : F = G)
      (c : Limits.Cone F) {A : Type u₁}
      (f : A → (Limits.getLimitCone G).cone.pt) (hpt : c.pt = A)
      (hπ : ∀ j, HEq (c.π.app j : c.pt → F.obj j)
        ((Limits.getLimitCone G).cone.π.app j ∘ f)) :
      HEq ((Limits.getLimitCone F).isLimit.lift c : c.pt → (Limits.getLimitCone F).cone.pt) f := by
    cases p
    cases hpt
    apply heq_of_eq
    apply Eq.symm
    have q : (↾f : c.pt ⟶ (Limits.getLimitCone F).cone.pt) = (Limits.getLimitCone F).isLimit.lift c := by
      apply (Limits.getLimitCone F).isLimit.uniq c
      intro j
      apply ConcreteCategory.ext_apply
      exact congrFun (eq_of_heq (hπ j)).symm
    exact congrArg (fun g : c.pt ⟶ (Limits.getLimitCone F).cone.pt => (g : c.pt → _)) q

  lemma canonical_heq (i : D) (self : CompactLRP.{u₁,u₂} D (rk i)) :
      HEq (MatchingObject.canonical i (layered_presheaf self).to_psh)
        (Sigma.fst : Y self i → MatchingObject i self.X.presheaf) := by
    unfold MatchingObject.Canonical.canonical
    apply lift_heq (congrArg (MatchingObject.functor i) (restrict_lp_to_psh self))
    · apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_n
    · intro ⟨⟨j, f, hij⟩⟩
      dsimp [MatchingObject.Canonical.canonical_cone, Presheaf.LayeredPresheaf.to_psh]
      unfold Presheaf.LayeredPresheaf.ToPsh.map
      split_ifs
      · rename_i h
        exfalso
        apply hij
        symm
        apply eq_of_map_of_rk_eq_rk f
        exact h
      · exact (heq_casts _ _ _).trans HEq.rfl
      · rename_i h₁ h₂
        exact False.elim (h₂ rfl)

  abbrev is_fibrant : ∀ (i : OfRank D n),
                      is_reedy_at i.point (restrict₄ i (layered_presheaf self).to_psh) := by
    intro ⟨i, rk_i_eq_n⟩
    induction rk_i_eq_n
    dsimp
    unfold is_reedy_at
    unfold is_fibration_strict
    exists ?map
    case map =>
      have : MatchingObject i (restrict₁ (layered_presheaf self).to_psh)
             = MatchingObject i self.X.presheaf := by
        rw [restrict_lp_to_psh]
      refine ?_ ∘ eqToHom this
      exact self.glueing i
    simp
    constructor
    · trans (Σ b : MatchingObject i self.X.presheaf, self.glueing i b)
      · exact sigma_transport _ _
      · symm
        apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_n
    · exact (sigma_fst_transport _ _).trans (canonical_heq i self).symm

  def to_lrp : LayeredReedyPresheaf.{u₁, u₂} D n where
    X := X self
    Y := Y self
    u := u self
    coh := coh self
    is_reedy := is_reedy self
    is_fibrant := is_fibrant self
  end ToLRP
  export ToLRP (to_lrp)

  section OfLRP
  variable (l : LayeredReedyPresheaf.{u₁, u₂} D n)

  def of_lrp : CompactLRP.{u₁, u₂} D n where
    X := {
      presheaf := l.X
      is_reedy := l.is_reedy
    }
    glueing i z := by
      dsimp only at z
      induction i with | mk i rk_i_eq_n =>
      induction rk_i_eq_n
      simp at z
      have := l.is_fibrant (OfRank.in_own_layer i)
      dsimp [is_reedy_at, is_fibration_strict] at this
      cases this with | mk can hello =>
      apply can
      suffices h : restrict₁ (restrict₄ i l.to_psh) = l.X
      · erw [h]
        exact z
      · refine CategoryTheory.Functor.ext ?object ?map
        · intro ⟨x⟩
          simp [restrict₄]
          apply Presheaf.LayeredPresheaf.ToPsh.obj_rk_lt_n
          simp
          intro rk_x_eq_rk_i
          apply Nat.lt_irrefl (rk i)
          conv => lhs; rw [← rk_x_eq_rk_i]
          apply x.rank_is_lt
        · intro ⟨x⟩ ⟨y⟩ f
          simp [restrict₁, restrict₄]
          apply ConcreteCategory.coe_ext
          apply Presheaf.LayeredPresheaf.ToPsh.map_rk_lt_n
          · exact Nat.ne_of_lt x.rank_is_lt
          · exact Nat.ne_of_lt y.rank_is_lt
          
  end OfLRP

  private theorem transport_cancel {A B C : Type _} (p : A = B) (q : B = C) (r : C = A) (a : A) :
      eqToHom (C := Type _) r (cast q (cast p a)) = a := by
    cases p
    cases q
    rfl

  def right_inv : Function.RightInverse (to_lrp (D := D) (n := n)) of_lrp := by
    intro c
    cases c with | mk X glueing =>
    unfold of_lrp to_lrp
    congr
    funext i z
    cases i with | mk i hi =>
    cases hi
    simp only
    dsimp [ToLRP.is_fibrant]
    change glueing (OfRank.in_own_layer i) (eqToHom (C := Type _) _ (cast _ (cast _ z))) = _
    congr 1
    apply transport_cancel

  private theorem sigma_cast {A B C : Type _} (p : A = B) (q : B = C) (E : C → Type _) :
      (Σ x : A, E (cast q (cast p x))) = (Σ y : C, E y) := by
    cases p
    cases q
    rfl

  private theorem left_inv_Y (l : LayeredReedyPresheaf.{u₁, u₂} D n) : (to_lrp (of_lrp l)).Y = l.Y := by
    funext i
    cases i with | mk i hi =>
    cases hi
    dsimp [to_lrp, ToLRP.Y, of_lrp]
    let fib := l.is_fibrant (OfRank.in_own_layer i)
    change (Σ z, fib.val (cast _ (cast _ z))) = l.Y _
    trans (Σ z, fib.val z)
    · exact sigma_cast _ _ (fun z => ^(fib.val z))
    · trans l.to_psh.obj (.op (OfRank.in_own_layer i).as_below)
      · exact congrArg Sigma.fst fib.property
      · exact Presheaf.LayeredPresheaf.ToPsh.obj_rk_n _ _ rfl

  private theorem family_cast_heq {A B C : Type _} (p : A = B) (q : B = C) (E : C → Typeₒ) :
      HEq (fun x : A => E (cast q (cast p x))) E := by
    cases p
    cases q
    rfl

  private theorem of_lrp_fiber_heq (l : LayeredReedyPresheaf.{u₁, u₂} D n) (i : OfRank D n) :
      HEq ((of_lrp l).glueing i) ((l.is_fibrant i).val) := by
    cases i with | mk i hi =>
    cases hi
    dsimp [of_lrp]
    change HEq (fun z => (l.is_fibrant (OfRank.in_own_layer i)).val (cast _ (cast _ z))) _
    apply family_cast_heq

  private theorem family_eqToHom_heq {A B : Type _} (p : A = B) (E : B → Typeₒ) :
      HEq (E ∘ eqToHom (C := Type _) p) E := by
    cases p
    rfl

  private theorem is_fibrant_fiber_heq (c : CompactLRP.{u₁, u₂} D n) (i : OfRank D n) :
      HEq ((ToLRP.is_fibrant c i).val) (c.glueing i) := by
    cases i with | mk i hi =>
    cases hi
    dsimp [ToLRP.is_fibrant]
    change HEq (c.glueing (OfRank.in_own_layer i) ∘ eqToHom (C := Type _) _) _
    apply family_eqToHom_heq

  private theorem fibration_heq.{u, v} {A A' : Type (max u v)} {B B' : Type v} {f : A → B} {g : A' → B'}
      (p : B = B') (a : is_fibration_strict.{u, v} f) (b : is_fibration_strict.{u, v} g)
      (h : HEq a.val b.val) : HEq a b := by
    cases p
    have hv : a.val = b.val := eq_of_heq h
    have ht : (⟨A, f⟩ : Σ T : Type _, T → B) = ⟨A', g⟩ :=
      a.property.symm.trans ((congrArg tot hv).trans b.property)
    have hA : A = A' := congrArg Sigma.fst ht
    cases hA
    have hfg : f = g := eq_of_heq (Sigma.mk.inj_iff.mp ht).2
    cases hfg
    exact heq_of_eq (Subtype.ext hv)

  private theorem left_inv_fibrant (l : LayeredReedyPresheaf.{u₁, u₂} D n)
      (hLP : (to_lrp (of_lrp l)).toLayeredPresheaf = l.toLayeredPresheaf) :
      HEq (to_lrp (of_lrp l)).is_fibrant l.is_fibrant := by
    apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    apply fibration_heq
    · exact congrArg (fun lp : Presheaf.LayeredPresheaf D n =>
        MatchingObject i.point (restrict₁ (restrict₄ i lp.to_psh))) hLP
    · exact (is_fibrant_fiber_heq (of_lrp l) i).trans (of_lrp_fiber_heq l i)

  private theorem sigma_fst_cast_heq {A B C : Type _} (p : A = B) (q : B = C) (E : C → Type _) :
      HEq (Sigma.fst : (Σ x : A, E (cast q (cast p x))) → A)
        (Sigma.fst : (Σ y : C, E y) → C) := by
    cases p
    cases q
    rfl

  private theorem fst_canonical_heq (l : LayeredReedyPresheaf.{u₁, u₂} D n) (i : OfRank D n) :
      HEq (Sigma.fst : (to_lrp (of_lrp l)).Y i → MatchingObject i.point (restrict₅ i l.X))
        (MatchingObject.canonical i.point (restrict₄ i l.to_psh)) := by
    cases i with | mk i hi =>
    cases hi
    let fib := l.is_fibrant (OfRank.in_own_layer i)
    apply HEq.trans _ (Sigma.mk.inj_iff.mp fib.property).2
    dsimp [to_lrp, ToLRP.Y, of_lrp]
    change HEq (Sigma.fst : (Σ z, fib.val (cast _ (cast _ z))) → _) _
    exact sigma_fst_cast_heq _ _ (fun z => ^(fib.val z))

  private theorem comp_heq {A A' B B' C C' : Type _} (hA : A = A') (hB : B = B') (hC : C = C')
      {f : B → C} {f' : B' → C'} (hf : HEq f f') {g : A → B} {g' : A' → B'} (hg : HEq g g') :
      HEq (f ∘ g) (f' ∘ g') := by
    cases hA
    cases hB
    cases hC
    exact heq_of_eq (congrArg₂ Function.comp (eq_of_heq hf) (eq_of_heq hg))

  private theorem matching_projection_heq (i : D) {F G : Psh (Below D (rk i))}
      (h : F = G) (j : (under i)ᵒᵖ) :
      HEq ((MatchingObject.limit_cone i F).cone.π.app j : MatchingObject i F → _)
        ((MatchingObject.limit_cone i G).cone.π.app j : MatchingObject i G → _) := by
    cases h
    rfl

  private theorem layered_reedy_ext (a b : LayeredReedyPresheaf.{u₁, u₂} D n)
      (h : a.toLayeredPresheaf = b.toLayeredPresheaf)
      (hr : HEq a.is_reedy b.is_reedy) (hf : HEq a.is_fibrant b.is_fibrant) : a = b := by
    cases a with | mk a ar af =>
    cases b with | mk b br bf =>
    dsimp only at h
    cases h
    cases eq_of_heq hr
    cases eq_of_heq hf
    rfl

  private theorem canonical_facet_heq (i : D) (l : Presheaf.LayeredPresheaf D (rk i))
      (j : Below D (rk i)) (f : j.point ⟶ i) (hij : i ≠ j.point) :
      HEq (l.u (i := OfRank.in_own_layer i) f)
        ((MatchingObject.limit_cone i (restrict₁ l.to_psh)).cone.π.app (.op ⟨j.point, f, hij⟩) ∘
          MatchingObject.canonical i l.to_psh) := by
    have fac := (MatchingObject.limit_cone i (restrict₁ l.to_psh)).isLimit.fac
      (MatchingObject.Canonical.canonical_cone i l.to_psh) (.op ⟨j.point, f, hij⟩)
    have hfac :
        (MatchingObject.limit_cone i (restrict₁ l.to_psh)).cone.π.app (.op ⟨j.point, f, hij⟩) ∘
          MatchingObject.canonical i l.to_psh =
        (MatchingObject.Canonical.canonical_cone i l.to_psh).π.app (.op ⟨j.point, f, hij⟩) := by
      exact congrArg (fun m : l.to_psh.obj (.op (Below.in_own_layer i)) ⟶ _ =>
        (m : l.to_psh.obj (.op (Below.in_own_layer i)) → _)) fac
    apply HEq.trans _ (heq_of_eq hfac.symm)
    dsimp [MatchingObject.Canonical.canonical_cone, Presheaf.LayeredPresheaf.to_psh]
    unfold Presheaf.LayeredPresheaf.ToPsh.map
    split_ifs
    · rename_i h
      exfalso
      apply hij
      symm
      apply eq_of_map_of_rk_eq_rk f
      exact h
    · exact (ToLRP.heq_casts _ _ _).symm
    · rename_i h₁ h₂
      exact False.elim (h₂ rfl)


  private theorem left_inv_u (l : LayeredReedyPresheaf.{u₁, u₂} D n) :
      HEq (@Presheaf.LayeredPresheaf.u D _ n (to_lrp (of_lrp l)).toLayeredPresheaf)
        (@Presheaf.LayeredPresheaf.u D _ n l.toLayeredPresheaf) := by
    apply Function.hfunext rfl
    intro i i' hi
    cases eq_of_heq hi
    apply Function.hfunext rfl
    intro j j' hj
    cases eq_of_heq hj
    apply Function.hfunext rfl
    intro f f' hf
    cases eq_of_heq hf
    cases i with | mk i rank_i =>
    cases rank_i
    have hij : i ≠ j.point := by
      intro h
      have hj := j.rank_is_lt
      rw [← h] at hj
      exact Nat.lt_irrefl _ hj
    change HEq
      ((MatchingObject.limit_cone i l.X).cone.π.app (.op ⟨j.point, f, hij⟩) ∘
        (Sigma.fst : (to_lrp (of_lrp l)).Y (OfRank.in_own_layer i) → _))
      (l.u f)
    have hp : restrict₁ l.to_psh = l.X :=
      congrArg Presheaf.LayeredPresheaf.X (Presheaf.LayeredPresheaf.right_inv l.toLayeredPresheaf)
    have hA : (to_lrp (of_lrp l)).Y (OfRank.in_own_layer i) =
        l.to_psh.obj (.op (Below.in_own_layer i)) :=
      (congrFun (left_inv_Y l) (OfRank.in_own_layer i)).trans
        (Presheaf.LayeredPresheaf.ToPsh.obj_rk_n l.toLayeredPresheaf (.op (Below.in_own_layer i)) rfl).symm
    apply HEq.trans _ (canonical_facet_heq i l.toLayeredPresheaf j f hij).symm
    apply comp_heq hA (congrArg (MatchingObject i) hp.symm)
      (congrArg (fun F : Psh (Below D (rk i)) => F.obj (.op j)) hp.symm)
    · exact matching_projection_heq i hp.symm _
    · exact fst_canonical_heq l (OfRank.in_own_layer i)

  private theorem left_inv_layer (l : LayeredReedyPresheaf.{u₁, u₂} D n) :
      (to_lrp (of_lrp l)).toLayeredPresheaf = l.toLayeredPresheaf := by
    apply Presheaf.LayeredPresheaf.ext
    · rfl
    · exact left_inv_Y l
    · exact left_inv_u l

  def left_inv : Function.LeftInverse (to_lrp (D := D) (n := n)) of_lrp := by
    intro l
    apply layered_reedy_ext _ _ (left_inv_layer l)
    · rfl
    · exact left_inv_fibrant l (left_inv_layer l)

  def compact_eqv_layered : LayeredReedyPresheaf D n ≃ CompactLRP D n where
    toFun := of_lrp
    invFun := to_lrp
    left_inv := left_inv
    right_inv := right_inv

  def compact_eqv_sigma : CompactLRP D n ≃ SigmaCompactLRP D n where
    toFun x :=
      let ⟨X, glueing⟩ := x
      ⟨X, glueing⟩
    invFun x :=
      let ⟨X, glueing⟩ := x
      ⟨X, glueing⟩
    left_inv := by
      intro
      rfl
    right_inv := by
      intro
      rfl

end CompactLRP

variable {D : Type*} [DirectCategory D] {n : Nat} in
def rdpsh_eqv_compact : ReedyPresheaf D (n+1) ≃ SigmaCompactLRP D n := by
  calc
    _ ≃ _ := by apply LayeredReedyPresheaf.eqv_of_layer_below
    _ ≃ _ := by apply CompactLRP.compact_eqv_layered
    _ ≃ _ := by apply CompactLRP.compact_eqv_sigma

end Tltt.ReedyFibrancy



namespace Fibrancy
def hello {α β : Type _} (p : α = β) (x : α) : (show α → α by rw [p]; exact id) x = x := by
  induction p
  rfl

end Fibrancy

end
