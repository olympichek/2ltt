import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Products
import Finite
import Misc

open CategoryTheory
open Limits (limit getLimitCone Cone LimitCone)
open Limits.IsLimit (conePointUniqueUpToIso)
open Limits.Types (terminalLimitCone)

noncomputable section
namespace Tltt

class DirectCategory (C : Type*) extends Category C where
  rank : @Functor C _ Nat (Preorder.smallCategory _)
  reflect_identity : ∀ x y : C, ∀ f : x ⟶ y, rank.obj x = rank.obj y →
                     (Sigma.mk (β := fun y => x ⟶ y) y f) = ⟨x, 𝟙 x⟩
export DirectCategory (rank)

abbrev rk {C : Type*} [DirectCategory C] (x : C) : Nat :=
  rank.obj x

abbrev leq_of_map {C : Type*} [DirectCategory C] {x y : C} (f : x ⟶ y) : rk x ≤ rk y :=
  rank.map f |>.down |>.down

abbrev eq_of_map_of_rk_eq_rk {C : Type*} [DirectCategory C] {x y : C} (f : x ⟶ y)
                             (p : rk x = rk y) : x = y := by
  have := DirectCategory.reflect_identity x y f p
  apply congrArg (·.fst) this.symm

@[simp]
theorem eq_id {C : Type*} [DirectCategory C] {x : C} (f : x ⟶ x) : f = 𝟙 x := by
  have := DirectCategory.reflect_identity x x f rfl
  simp at this
  assumption

@[ext]
structure OfRank (C : Type*) [DirectCategory C] (n : Nat) where
  point : C
  rank_is : rk point = n

namespace OfRank
  variable {C : Type*} [DirectCategory C]

  def in_own_layer (i : C) : OfRank C (rk i) where
    point := i
    rank_is := by rfl

  instance (i : C) : CoeDep C i (OfRank C (rk i)) where
    coe := OfRank.in_own_layer i

  @[simp]
  theorem in_own_layer_point (i : C) : (in_own_layer i).point = i := by
    rfl

  instance [DecidableEq C] (n : Nat) : DecidableEq (OfRank C n) := by
    intro x y
    if h : x.point = y.point then
      apply Decidable.isTrue
      ext
      assumption
    else
      apply Decidable.isFalse
      intro
      apply h
      congr

end OfRank

@[ext]
structure Below (C : Type _) [DirectCategory C] (n : Nat) where
  point : C
  rank_is_lt : rk point < n

namespace Below
  variable {C : Type*} [DirectCategory C]

  instance (n : Nat) : Category (Below C n) where
    Hom a b := a.point ⟶ b.point
    id a := 𝟙 a.point
    comp {a b c} f g := f ≫ g
    id_comp := by
      intro a b f
      simp
    comp_id := by
      intro a b f
      simp
    assoc := by
      intro a b c d f g h
      simp

  def forget {n : Nat} : Below C n ⥤ C where
    obj x := x.point
    map {a b} f := f
    map_id := by
      intro
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem forget.beta_obj {n : Nat} (x : Below C n) : forget.obj x = x.point := by
    rfl

  instance (C : Type _) [DirectCategory C] (n : Nat) : DirectCategory (Below C n) where
    rank := forget ⋙ rank
    reflect_identity := by
      intro x y f p
      simp at p
      have q := DirectCategory.reflect_identity _ _ f p
      simp at q ⊢
      have ⟨q₁, q₂⟩ := q
      apply And.intro
      · ext
        exact q₁
      · exact q₂

  abbrev transport_fwd {n : Nat} (i : OfRank C n) : Below C n ⥤ Below C (rk i.point) := by
    induction i with | mk point rank_is =>
    induction rank_is
    apply Functor.id

  abbrev transport_bwd {n : Nat} (i : OfRank C n) : Below C (rk i.point) ⥤ Below C n := by
    induction i with | mk point rank_is =>
    induction rank_is
    apply Functor.id

  -- abbrev transport' {n : Nat} (i : OfRank C n) : Below C (rk i.point + 1) ⥤ Below C (n+1) := by
  --   induction i with | mk i rank_is =>
  --   induction rank_is
  --   apply Functor.id

  def not_below_zero (x : Below C 0) : False := by
    apply Nat.not_lt_zero
    apply x.rank_is_lt

  def generic {n : Nat} : Below C n ≃ { point : C // rk point < n } where
    toFun := by
      intro ⟨point, rank_is_lt⟩
      exact ⟨point, rank_is_lt⟩
    invFun := by
      intro ⟨point, rank_is_lt⟩
      exact ⟨point, rank_is_lt⟩
    left_inv := by
      intro
      rfl
    right_inv := by
      intro
      rfl

  def up {n : ℕ} (i : Below C n) : Below C (n+1) where
    point := i.point
    rank_is_lt := by
      trans n
      apply i.rank_is_lt
      constructor

  def in_own_layer (i : C) : Below C (rk i + 1) where
    point := i
    rank_is_lt := by simp

  instance (i : C) : CoeDep C i (Below C (rk i + 1)) where
    coe := Below.in_own_layer i

  instance of_below (n : Nat) : Coe (Below C n) (Below C (n+1)) where
    coe := by
      intro ⟨x, _⟩
      exists x
      apply Nat.lt_succ_of_lt
      assumption

  instance of_rank {n : Nat} : Coe (OfRank C n) (Below C (n+1)) where
    coe := by
      intro ⟨x, _⟩
      exists x
      simp [*]

  def inclusion (C : Type*) [DirectCategory C] (n : Nat) : Below C n ⥤ Below C (n+1) where
    obj x := ↑x
    map {_ _} f := f
    map_id := by
      intros
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem inclusion_obj {n : Nat} (x : Below C n) : (inclusion C n |>.obj x) = ↑x := by
    rfl

  @[simp]
  theorem inclusion_map {n : Nat} {x y : Below C n} (f : x ⟶ y) : (inclusion C n |>.map f) = f := by
    rfl

  def eqv_empty_of_zero : Below C 0 ≃ Empty where
    toFun x := by
      exfalso
      apply x.not_below_zero
    invFun x :=
      x.elim
    left_inv x := by
      exfalso
      apply x.not_below_zero
    right_inv x :=
      x.elim

  def forget' {n : Nat} {i : Below C n} : Below C (rk i + 1) ⥤ Below C n where
    obj x := .mk x.point <| calc
      rk x ≤ rk i := by
        apply Nat.le_of_lt_succ
        apply rank_is_lt
      rk i < n := by apply rank_is_lt
    map {x y} f := f
    map_id := by
      intro
      rfl
    map_comp := by
      intros
      rfl

  @[simp]
  theorem rk_of_forget' {n : Nat} {i : Below C n} (j : Below C (rk i + 1)) : rk (forget'.obj j) = rk j := by
    rfl

  def of_succ_of_rk_ne {n : Nat} (x : Below C (n+1)) (p : rk x ≠ n) : Below C n :=
    .mk x.point <| by
      apply Nat.lt_of_le_of_ne
      · apply Nat.le_of_lt_succ
        exact x.rank_is_lt
      · assumption

  @[simp]
  theorem of_succ_of_rk_ne.beta_point {n : Nat} (x : Below C (n+1)) (p : rk x ≠ n)
                                      : (of_succ_of_rk_ne x p).point = x.point := by
    rfl

end Below

def empty.functor (D : Type _) [DirectCategory D] : Psh (Below D 0) where
  obj x := by
    exfalso
    apply x.unop.not_below_zero
  map {x _} _ := by
    exfalso
    exact x.unop.not_below_zero
  map_id := by
    intro ⟨x⟩
    exfalso
    exact x.not_below_zero
  map_comp := by
    intro ⟨x⟩
    exfalso
    exact x.not_below_zero

def OfRank.as_below {C : Type*} [DirectCategory C] {n : Nat} (i : OfRank C n) : Below C (n+1) where
  point := i.point
  rank_is_lt := by simp [i.rank_is]

instance {C : Type*} [DirectCategory C] {P : C → Prop} : DirectCategory { x : C // P x } where
  rank := {
    obj := (rank.obj <| Subtype.val ·)
    map := rank.map
    map_comp := by
      intros
      apply rank.map_comp
    map_id := by
      intros
      simp
  }
  reflect_identity := by
    intro x y f e
    have := DirectCategory.reflect_identity x.val y.val f e
    simp
    simp at this
    cases this
    constructor
    apply Subtype.coe_eq_of_eq_mk
    repeat assumption


@[simp]
def cast_cast_eq {D : Type*} [DirectCategory D] {n : Nat} (x : Below D (n+1)) (p : rk x ≠ n)
                 : ↑(x.of_succ_of_rk_ne p) = x := by
  rfl

def under {C : Type _} [Category C] (x : C) :=
  Σ y : C, { _f : y ⟶ x // x ≠ y }

instance under_is_category {C : Type _} [ι : Category C] (x : C) : Category (under x) where
  Hom a b := { f : a.1 ⟶ b.1 // f ≫ b.2.1 = a.2.1 }
  id a := ⟨𝟙 a.1, by apply ι.id_comp⟩
  comp {a b c} f g := ⟨f.1 ≫ g.1, by rw [ι.assoc, g.2, f.2]⟩
  id_comp := by
    intro a b f
    simp
  comp_id := by
    intro a b f
    simp
  assoc := by
    intros
    simp

def under.inclusion (C : Type _) [DirectCategory C] (x : C) : under x ⥤ (Below C (rk x)) where
  obj y := .mk y.fst <| by
    apply Nat.lt_of_le_of_ne
    · apply leq_of_map
      apply y.snd.val
    · intro rk_y_eq_rk_x
      apply y.snd.prop
      have := DirectCategory.reflect_identity _ _ y.snd.val rk_y_eq_rk_x
      apply congrArg (·.fst) this
  map {_ _} f := f.val
  map_id := by
    intros
    rfl
  map_comp := by
    intros
    rfl

abbrev MatchingObject.functor {D : Type*} [DirectCategory D] (i : D)
                              (X : Psh (Below D (rk i))) : Psh (under i) :=
  (under.inclusion D i).op ⋙ X

def MatchingObject.limit_cone {D : Type*} [DirectCategory D] (i : D)
                              (X : Psh (Below D (rk i))) : LimitCone (functor i X) :=
  getLimitCone <| MatchingObject.functor i X

def MatchingObject {D : Type*} [DirectCategory D] (i : D) (X : Psh (Below D (rk i))) : Type _ :=
  MatchingObject.limit_cone i X |>.cone |>.pt

section Restrictions
variable {D : Type*} [DirectCategory D] {n : ℕ}

def restrict₁ (F : Psh (Below D (n+1))) : Psh (Below D n) :=
  (Below.inclusion _ _).op ⋙ F

@[simp]
theorem restrict₁.obj_beta (F : Psh (Below D (n+1))) (i : Below D n)
                           : (restrict₁ F).obj (.op i) = F.obj (.op i) := by
  rfl

-- @[simp]
def restrict₂ (i : Below D n) (F : Psh (Below D n)) : Psh (Below D (rk i + 1)) :=
  Below.forget'.op ⋙ F

-- @[simp]
def restrict₃ (F : Psh D) : Psh (Below D n) :=
  Below.forget.op ⋙ F

@[simp]
theorem restrict₃.obj_beta (F : Psh D) (i : Below D n)
                           : (restrict₃ F).obj (.op i) = F.obj (.op i.point) := by
  rfl

@[simp]
def restrict₃.beta (F : Psh D) (x : Below D n) : (restrict₃ F).obj (.op x) = F.obj (.op x.point) := by
  rfl

-- @[simp]
def restrict₄ (i : OfRank D n) (F : Psh (Below D (n+1))) : Psh (Below D (rk i.point + 1)) :=
  (Below.forget' (i := i.as_below)).op ⋙ F

@[simp]
theorem restrict₄.beta (i : D) (F : Psh (Below D (rk i + 1))) : restrict₄ ⟨i, rfl⟩ F = F := by
  rfl

def func_of_rk_eq (i : D) (p : rk i = n) : Below D (rk i) ⥤ Below D n := by
  induction p
  apply Functor.id

@[simp]
theorem func_of_rk_eq_refl (i : D) (p : rk i = rk i) : func_of_rk_eq i p = Functor.id _ := by
  rfl

def restrict₅ (i : OfRank D n) (F : Psh (Below D n)) : Psh (Below D (rk i.point)) :=
  (func_of_rk_eq i.point i.rank_is).op ⋙ F

@[simp]
theorem restrict₅.refl_beta (i : D) (F : Psh (Below D (rk i))) (p : rk i = rk i) : restrict₅ ⟨i, p⟩ F = F := by
  rfl

def restrict₆ (F G : Psh D) (η : NatTrans F G) : NatTrans (restrict₃ (n := n) F) (restrict₃ G) where
  app := by
    intro ⟨x⟩
    simp
    apply η.app
  naturality := by
    intros
    simp
    apply η.naturality
end Restrictions

namespace MatchingObject
  variable {D : Type*} [DirectCategory D] (i : D)

  namespace Canonical
    variable (X : Psh (Below D (rk i + 1)))
    def canonical_cone : Cone <| functor i (restrict₁ X) where
      pt := X.obj <| .op i
      π := {
        app j := X.map (show
          (↑((under.inclusion D i).obj j.unop) : Below D (rk i + 1)) ⟶
            Below.in_own_layer i from j.unop.snd.val).op
        naturality := by
          intro a b f
          change X.map _ = X.map _ ≫ X.map _
          erw [← X.map_comp]
          congr 1
          exact congrArg Quiver.Hom.op f.unop.property.symm
      }

    def canonical : X.obj (.op i) → MatchingObject i (restrict₁ X) :=
      limit_cone i (restrict₁ X) |>.isLimit |>.lift <| canonical_cone i X

    section uniqueness
    variable (f : X.obj (.op i) → MatchingObject i (restrict₁ X))

    def is_unique (q : ∀ j, (limit_cone i (restrict₁ X)).cone.π.app j ∘ f = (canonical_cone i X).π.app j)
                : f = canonical i X := by
      unfold canonical
      have h : (↾f : X.obj (.op i) ⟶ MatchingObject i (restrict₁ X)) =
          (limit_cone i (restrict₁ X)).isLimit.lift (canonical_cone i X) := by
        apply (limit_cone i (restrict₁ X)).isLimit.uniq (canonical_cone i X)
        intro j
        apply ConcreteCategory.ext_apply
        exact congrFun (q j)
      exact congrArg (fun g : X.obj (.op i) ⟶ MatchingObject i (restrict₁ X) =>
        (g : X.obj (.op i) → MatchingObject i (restrict₁ X))) h
    end uniqueness
  end Canonical
  export Canonical (canonical)

  def eqv_unit_of_card_zero [d : DirectCategory D] (i : D) {ι : Finite (Below D (rank.obj i))}
                            (X : (Below D (rank.obj i))ᵒᵖ ⥤ Type _) (p : |Below D (rank.obj i)| = 0)
                            : MatchingObject i X ≃ PUnit := by
    apply Iso.toEquiv
    have : IsEmpty (under i)ᵒᵖ := by
      constructor
      intro j
      apply Nat.not_lt_zero
      apply Fin.isLt
      rw [← p]
      apply ι.equiv.toFun
      constructor
      rotate_left
      · exact j.unop.fst
      · apply Nat.lt_of_le_of_ne
        · apply PLift.down
          apply ULift.down
          apply rank.map
          apply j.unop.snd.val
        · intro rank_j_eq_rank_i
          apply j.unop.snd.prop
          apply congrArg Sigma.fst
            <| d.reflect_identity j.unop.fst i j.unop.snd.val rank_j_eq_rank_i
    apply conePointUniqueUpToIso (t := unit_cone_of_presheaf_over_empty _)
    · apply LimitCone.isLimit
    · apply unit_cone_is_limit

end MatchingObject

namespace Presheaf
universe v w
@[ext]
structure LayeredPresheaf (D : Type*) [DirectCategory D] (n : Nat) where
  X : (Below D n)ᵒᵖ ⥤ Type v
  Y : OfRank D n → Type w
  u {i : OfRank D n} {j : Below D n} : (j.point ⟶ i.point) → (Y i → X.obj (.op j))
  coh {i : OfRank D n} {j j' : Below D n} (f : j.point ⟶ i.point) (g : j' ⟶ j)
      : (X.map (.op g)) ∘ (u f) = u (g ≫ f)

namespace LayeredPresheaf
variable {D : Type*} [DirectCategory D] {n : Nat}

def ext' (a b : LayeredPresheaf D n) (eqX : a.X = b.X) (eqY : a.Y = b.Y)
         (eqU : ∀ {i : OfRank D n} {j : Below D n} (f : j.point ⟶ i.point),
                eqToHom (C := Type _) (by rw [eqX]) ∘ a.u f ∘ eqToHom (C := Type _) (by rw [eqY]) = b.u f)
         : a = b := by
  induction a with | mk Xa Ya ua _ =>
  induction b with | mk Xb Yb ub _ =>
  cases eqX
  cases eqY
  simp
  funext i j f
  simp at eqU
  apply eqU

def of_psh (F : Psh (Below D (n+1))) : LayeredPresheaf D n where
  X := restrict₁ F
  Y i := F.obj <| .op <| .mk i.point <| by
    erw [i.rank_is]
    simp
  u := by
    intro i j f
    change F.obj (.op i.as_below) → F.obj (.op ((Below.inclusion D n).obj j))
    exact fun x => F.map (show (Below.inclusion D n).obj j ⟶ i.as_below from f).op x
  coh := by
    intro i j j' f g
    simp
    let iup : Below D (n+1) := i
    let jup : Below D (n+1) := j
    let j'up : Below D (n+1) := j'
    let fup : jup ⟶ iup := f
    let gup : j'up ⟶ jup := g
    show F.map gup.op ∘ F.map fup.op = F.map (fup.op ≫ gup.op)
    rw [F.map_comp]
    rfl

namespace ToPsh
  variable (self : LayeredPresheaf D n)

  def obj (i : (Below D (n+1))ᵒᵖ) : Type _ :=
    if h : rk i.unop = n then
      self.Y ⟨i.unop.point, h⟩
    else
      self.X.obj <| .op <| i.unop.of_succ_of_rk_ne  h

  def obj_rk_n (i : (Below D (n+1))ᵒᵖ) (h : rk i.unop = n)
                       : obj self i = self.Y ⟨i.unop.point, h⟩ := by
    unfold obj
    rw [dif_pos]

  def obj_rk_lt_n (i : (Below D (n+1))ᵒᵖ) (h : rk i.unop ≠ n)
                  : let i' : Below D n := i.unop.of_succ_of_rk_ne  h
                    obj self i = (self.X.obj (.op i')) := by
    unfold obj
    rw [dif_neg]

  def map {j i : (Below D (n+1))ᵒᵖ} (f : j ⟶ i) : obj self j → obj self i :=
    if h₁ : rk i.unop = n then
      have h₂ : rk j.unop = n := by
        apply Nat.le_antisymm
        · apply Nat.le_of_lt_succ
          apply j.unop.rank_is_lt
        · calc
            _ = _ := h₁.symm
            _ ≤ _ := by
              apply leq_of_map
              exact f.unop
      have i_eq_j : i = j := by
        have := eq_of_map_of_rk_eq_rk (x := i.unop) (y := j.unop) f.unop <| by
          trans n
          · exact h₁
          · exact h₂.symm
        show ⟨i.unop⟩ = j
        rw [this]
      eqToHom <| show obj self j = obj self i by rw [i_eq_j]
    else if h₂ : rk j.unop = n then
      let i' : (Below D n)ᵒᵖ := .op <| i.unop.of_succ_of_rk_ne  (by trivial)
      let j' : OfRank D n := ⟨j.unop.point, h₂⟩
      have Xi_to_obj_i : self.X.obj i' → obj self i := eqToHom (C := Type _) <| by
        rw [obj_rk_lt_n]
      have obj_j_to_Yj : obj self j → self.Y j' := eqToHom (C := Type _) <| by rw [obj_rk_n]
      have Yj_to_Xi : self.Y j' → self.X.obj i' := self.u f.unop
      Xi_to_obj_i ∘ Yj_to_Xi ∘ obj_j_to_Yj
    else
      let i' : (Below D n)ᵒᵖ := .op <| i.unop.of_succ_of_rk_ne (by trivial)
      let j' : (Below D n)ᵒᵖ := .op <| j.unop.of_succ_of_rk_ne (by trivial)
      have Xi_to_obj_i : self.X.obj i' → obj self i := eqToHom (C := Type _) <| by
        rw [obj_rk_lt_n]
      have obj_j_to_Xi : obj self j → self.X.obj j' := eqToHom (C := Type _) <| by
        rw [obj_rk_lt_n]
      Xi_to_obj_i ∘ self.X.map f ∘ obj_j_to_Xi

  def map_rk_lt_n {j i : (Below D (n+1))ᵒᵖ}  (f : j ⟶ i) (p : rk j.unop ≠ n) (q : rk i.unop ≠ n)
                  : map self f = eqToHom (obj_rk_lt_n self i q).symm
                                 ∘ self.X.map f
                                 ∘ eqToHom (obj_rk_lt_n self j p) := by
    unfold map
    dsimp only
    split_ifs <;> trivial

  def map_id (i : (Below D (n+1))ᵒᵖ) : map self (CategoryStruct.id i) = id := by
    unfold map
    dsimp only
    split_ifs
    · generalize_proofs
      rename_i p
      cases p
      rfl
    · erw [self.X.map_id]
      apply something
  where
    something {α β : Type _} (p : α = β) (q : β = α)
                : eqToHom (C := Type _) q ∘ id ∘ eqToHom (C := Type _) p = id := by
      induction p
      rfl

  def map_comp {k j i : (Below D (n+1))ᵒᵖ} (f : k ⟶ j) (g : j ⟶ i)
               : map self (f ≫ g) = map self g ∘ map self f := by
    unfold map
    split_ifs <;> dsimp only
    · generalize_proofs
      rename_i p₁ p₂ p₃
      have : i = j := by
        show Opposite.op i.unop = ⟨j.unop⟩
        apply congrArg Opposite.op
        apply eq_of_map_of_rk_eq_rk
        · exact g.unop
        · trans n
          repeat first | assumption | apply Eq.symm
      induction this
      simp
    · exfalso
      rename_i rk_i_eq_n rk_j_neq_n rk_k_eq_n
      apply rk_j_neq_n
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply j.unop.rank_is_lt
      · conv => lhs; rw [← rk_i_eq_n]
        apply leq_of_map
        exact g.unop
    · exfalso
      rename_i rk_i_eq_n rk_j_neq_n rk_k_neq_n
      apply rk_j_neq_n
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply j.unop.rank_is_lt
      · conv => lhs; rw [← rk_i_eq_n]
        apply leq_of_map
        exact g.unop
    · have : j = k := by
        show Opposite.op j.unop = ⟨_⟩
        apply congrArg Opposite.op
        apply eq_of_map_of_rk_eq_rk
        · exact f.unop
        · trans n
          repeat first | assumption | apply Eq.symm
      induction this
      simp
    · let i' : Below D n := i.unop.of_succ_of_rk_ne (by assumption)
      let j' : Below D n := j.unop.of_succ_of_rk_ne (by assumption)
      let k' : OfRank D n := ⟨k.unop.point, by assumption⟩
      let f' : j'.point ⟶ k'.point := f.unop
      let g' : i' ⟶ j' := g.unop
      have : _ = self.u (i := k') (j := i') (f ≫ g).unop :=
        self.coh (i := k') (j := j') (j' := i') f' g'
      rw [← this]
      generalize_proofs
      rename_i pf₁ pf₂ pf₃ pf₄ pf₅
      conv =>
        rhs
        rw [comp_assoc,
            comp_assoc (eqToHom pf₁) _ (eqToHom pf₃),
            ← comp_assoc _ _ (eqToHom pf₅),
            eqToHom_eq_id pf₃ pf₅
            ]
        dsimp
        rw [← comp_assoc, comp_assoc _ _ (eqToHom pf₂)]
      rfl
    · exfalso
      rename_i rk_i_neq_n rk_j_neq_n rk_k_eq_n
      apply rk_j_neq_n
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply k.unop.rank_is_lt
      · conv => lhs; rw [← rk_k_eq_n]
        apply leq_of_map
        exact f.unop
    · let i' : Below D n := i.unop.of_succ_of_rk_ne (by assumption)
      let j' : Below D n := j.unop.of_succ_of_rk_ne (by assumption)
      let k' : Below D n := k.unop.of_succ_of_rk_ne (by assumption)
      generalize_proofs
      rename_i pf₁ pf₂ pf₃ pf₄ pf₅
      conv =>
        rhs
        rw [comp_assoc,
            comp_assoc (eqToHom pf₁) _ (eqToHom pf₃),
            ← comp_assoc _ _ (eqToHom pf₅),
            eqToHom_eq_id pf₃ pf₅
            ]
        dsimp
        rw [← comp_assoc, comp_assoc _ _ (eqToHom pf₂)]
      erw [self.X.map_comp (X := .op k') (Y := .op j') (Z := .op i') f g]
      rfl
  where
    eqToHom_eq_id {α β : Type _} (p : α = β) (q : β = α) : eqToHom p ∘ eqToHom q = id := by
      induction p
      rfl
    comp_assoc {α β γ δ : Type _} (f : γ → δ) (g : β → γ) (h : α → β) : f ∘ (g ∘ h) = (f ∘ g) ∘ h := rfl

end ToPsh

def to_psh (self : LayeredPresheaf D n) : Psh (Below D (n+1)) where
  obj := ToPsh.obj self
  map f := ↾(ToPsh.map self f)
  map_id i := by
    apply ConcreteCategory.ext_apply
    exact congrFun (ToPsh.map_id self i)
  map_comp f g := by
    apply ConcreteCategory.ext_apply
    exact congrFun (ToPsh.map_comp self f g)

@[simp]
def left_inv : Function.LeftInverse to_psh (of_psh (D := D) (n := n)) := by
  intro F
  induction F with | mk obj map map_id map_comp =>
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    unfold of_psh to_psh ToPsh.obj
    dsimp only
    split_ifs <;> rfl
  · intro j i f
    unfold of_psh to_psh ToPsh.map
    dsimp only at map_id map_comp ⊢
    split_ifs
    · have : i = j := by
        show Opposite.op i.unop = ⟨_⟩
        apply congrArg Opposite.op
        apply eq_of_map_of_rk_eq_rk
        · exact f.unop
        · apply Nat.le_antisymm
          · apply leq_of_map
            exact f.unop
          · calc
              _ ≤ n := by
                apply Nat.le_of_lt_succ
                apply j.unop.rank_is_lt
              _ = _ := by apply Eq.symm; assumption
      induction this
      induction f
      rename_i f
      rw [eq_id (x := i.unop) f]
      have : { unop := 𝟙 i.unop } = 𝟙 i := by
        rfl
      rw [this]
      simp [map_id]
      rfl
    · rename_i h₁ h₂
      exfalso
      apply h₂
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply j.unop.rank_is_lt
      · conv => lhs; rw [← h₁]
        apply leq_of_map
        exact f.unop
    · rfl
    · rfl

def left_inv.hello {α β : Type v} (p : α = β) (q : β = α)
    : eqToHom p ∘ id ∘ eqToHom q = id := by
  induction p
  rfl

@[simp]
def right_inv : Function.RightInverse to_psh (of_psh (D := D) (n := n)) := by
  intro ⟨X, Y, u, coh⟩
  unfold of_psh to_psh
  dsimp only
  apply LayeredPresheaf.ext'
  case eqX =>
    dsimp only
    apply CategoryTheory.Functor.ext
    · intro j i f
      unfold ToPsh.map restrict₁
      simp
      split_ifs
      · exfalso
        apply Nat.lt_irrefl n
        rename_i h
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
      · exfalso
        apply Nat.lt_irrefl n
        rename_i h
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
      · rfl
    · intro i
      unfold ToPsh.obj restrict₁
      simp
      split_ifs
      · exfalso
        apply Nat.lt_irrefl n
        rename_i h
        conv => lhs; rw [← h]
        apply Below.rank_is_lt
      · rfl
  case eqY =>
    unfold ToPsh.obj
    funext i
    simp
    split_ifs <;> try rfl
    exfalso
    rename_i h
    apply h
    apply i.rank_is
  case eqU =>
    intro i j f
    unfold ToPsh.map
    simp only
    split_ifs
    · exfalso
      rename_i h
      apply Nat.lt_irrefl n
      conv => lhs; rw [← h]
      simp
      apply Below.rank_is_lt
    · simp only [id, TypeCat.ofHom_apply]
      change (eqToHom (C := Type _) _ ∘ eqToHom (C := Type _) _) ∘ u f ∘
        (eqToHom (C := Type _) _ ∘ eqToHom (C := Type _) _) = u f
      erw [eqToHom_simp, eqToHom_simp]
      rfl
    · exfalso
      rename_i h
      apply h
      apply OfRank.rank_is

def eqv_to_next_layer (D : Type*) [DirectCategory D] (n : Nat)
                      : Psh (Below D (n+1)) ≃ LayeredPresheaf D n where
  toFun F := of_psh F
  invFun lp := to_psh lp
  left_inv := left_inv
  right_inv := right_inv

end LayeredPresheaf
end Presheaf

end Tltt
end
