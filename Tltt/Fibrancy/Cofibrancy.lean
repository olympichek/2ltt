import Tltt.Fibrancy

noncomputable section
namespace Tltt.Fibrancy
open Hott
universe u v w u'

/-- Dependent products over `α` preserve fibrancy at the specified universe. -/
class IsPiFibrant (α : Type u) : Type (max u (v+1) (w+1)) where
  pi_fibrant {β : α → Type v} : (∀ a, IsFibrantWeak.{v,w} (β a)) →
    IsFibrantWeak.{max u v,w} (∀ a, β a)


@[instance_reducible]
def finite_pi_fibrant (α : Type u) [Finite α] : IsPiFibrant.{u,v,w} α where
  pi_fibrant h := by
    classical
    exact fintype_is_cofibrant (β_is_fib := h)

@[instance_reducible]
def fibrant_pi_fibrant {α : Type u} (h : IsFibrantWeak.{u,w} α) :
    IsPiFibrant.{u,v,w} α where
  pi_fibrant hβ := Tltt.Fibrancy.pi_fibrant h hβ

/-- Preservation of fibrant products is invariant under equivalence of outer types. -/
@[instance_reducible]
def pi_fibrant_of_equiv {α : Type u} {α' : Type u'}
    (h : IsPiFibrant.{u,v,w} α) (e : α ≃ α') : IsPiFibrant.{u',v,w} α' where
  pi_fibrant {β} hβ :=
    fibrant_of_eqv_fibrant (h.pi_fibrant (fun a => hβ (e a)))
      (pi_eqv_of_eqv_pre e).symm

/-- A constant decidable restriction preserves the product-closure property. -/
@[instance_reducible]
def pi_fibrant_subtype_const {α : Type u} (h : IsPiFibrant.{u,v,w} α) (p : Prop) [Decidable p] :
    IsPiFibrant.{u,v,w} {a : α // p} := by
  by_cases hp : p
  · exact pi_fibrant_of_equiv h {
      toFun := fun a => ⟨a, hp⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  · exact pi_fibrant_of_equiv (finite_pi_fibrant (Fin 0)) {
      toFun := Fin.elim0
      invFun := fun a => False.elim (hp a.property)
      left_inv := fun a => Fin.elim0 a
      right_inv := fun a => False.elim (hp a.property)
    }


/-- A chosen inner representative together with its inner contraction. -/
class IsTriviallyFibrant (α : Type u) extends IsFibrantWeak.{u,v} α where
  contractible : Typeₒ.is_contractible obj_type

@[instance_reducible]
def trivially_fibrant_of_equiv {α : Type u} {β : Type u'}
    (h : IsTriviallyFibrant.{u,w} α) (e : α ≃ β) : IsTriviallyFibrant.{u',w} β where
  obj_type := h.obj_type
  fibrancy := h.fibrancy.trans e
  contractible := h.contractible

@[instance_reducible]
def unit_is_trivially_fibrant : IsTriviallyFibrant.{u,w} PUnit where
  obj_type := Unitₒ.{w}
  fibrancy := unit_is_fibrant.fibrancy
  contractible := by
    exhibitₒ ()ₒ
    introₒ x
    rw [Unitₒ.eq_unit x]
    rflₒ

@[instance_reducible]
def prod_is_trivially_fibrant {α : Type u} {β : Type v}
    (hα : IsTriviallyFibrant.{u,w} α) (hβ : IsTriviallyFibrant.{v,w} β) :
    IsTriviallyFibrant.{max u v,w} (α × β) where
  toIsFibrantWeak := prod_is_fibrant hα.toIsFibrantWeak hβ.toIsFibrantWeak
  contractible := by
    exhibitₒ ⟪hα.contractible₊1, hβ.contractible₊1⟫
    introₒ z
    apply Sigmaₒ.eq_constructor.combine
    exhibitₒ hα.contractible₊2 z₊1
    exact (hβ.contractible₊2 _)⁻¹ ⬝ hβ.contractible₊2 _

@[instance_reducible]
def finite_pi_trivially_fibrant {α : Type u} [Finite α] {β : α → Type v}
    (hβ : ∀ a, IsTriviallyFibrant.{v,w} (β a)) :
    IsTriviallyFibrant.{max u v,w} (∀ a, β a) := by
  classical
  generalize h : |α| = n
  induction n generalizing α with
  | zero =>
    apply trivially_fibrant_of_equiv
    · exact unit_is_trivially_fibrant.{0,w}
    · apply Equiv.symm
      apply Finite.from_card_zero_eqv_unit (α := α)
      assumption
  | succ n ih =>
    have z : α := Finite.el_of_card_succ <| by
      rw [h]
      simp
    let previous := { x : α // x ≠ z }
    apply trivially_fibrant_of_equiv (α := (∀ x : previous, β ↑x) × (β z))
    · apply prod_is_trivially_fibrant
      · apply ih
        · intro x
          apply hβ
        rw [Finite.card_of_remove_one, h]
        simp
      · apply hβ
    · apply Equiv.symm
      apply Finite.pi_eqv_pi_prod

@[instance_reducible]
def fibrant_pi_trivially_fibrant {α : Type u} {β : α → Type v}
    (hα : IsFibrantWeak.{u,w} α) (hβ : ∀ a, IsTriviallyFibrant.{v,w} (β a)) :
    IsTriviallyFibrant.{max u v,w} (∀ a, β a) where
  toIsFibrantWeak := pi_fibrant hα (fun a => (hβ a).toIsFibrantWeak)
  contractible := by
    apply Extensionality.weak_fun_ext
    introₒ a
    exact (hβ (hα.fibrancy a)).contractible

/-- Cofibrancy at the specified family and witness universes preserves both fibrant
and contractible fibrant dependent products. -/
class IsCofibrant (α : Type u) extends IsPiFibrant.{u,v,w} α where
  pi_trivially_fibrant {β : α → Type v} : (∀ a, IsTriviallyFibrant.{v,w} (β a)) →
    IsTriviallyFibrant.{max u v,w} (∀ a, β a)

@[instance_reducible]
def finite_is_cofibrant (α : Type u) [Finite α] : IsCofibrant.{u,v,w} α where
  toIsPiFibrant := finite_pi_fibrant α
  pi_trivially_fibrant := finite_pi_trivially_fibrant

@[instance_reducible]
def fibrant_is_cofibrant {α : Type u} (hα : IsFibrantWeak.{u,w} α) :
    IsCofibrant.{u,v,w} α where
  toIsPiFibrant := fibrant_pi_fibrant hα
  pi_trivially_fibrant := fibrant_pi_trivially_fibrant hα

@[instance_reducible]
def cofibrant_of_equiv {α : Type u} {α' : Type u'}
    (h : IsCofibrant.{u,v,w} α) (e : α ≃ α') : IsCofibrant.{u',v,w} α' where
  pi_fibrant hβ :=
    fibrant_of_eqv_fibrant (h.pi_fibrant (fun a => hβ (e a)))
      (pi_eqv_of_eqv_pre e).symm
  pi_trivially_fibrant hβ :=
    trivially_fibrant_of_equiv (h.pi_trivially_fibrant (fun a => hβ (e a)))
      (pi_eqv_of_eqv_pre e).symm

@[instance_reducible]
def cofibrant_subtype_const {α : Type u} (h : IsCofibrant.{u,v,w} α)
    (p : Prop) [Decidable p] : IsCofibrant.{u,v,w} {a : α // p} := by
  by_cases hp : p
  · exact cofibrant_of_equiv h {
      toFun := fun a => ⟨a, hp⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  · exact cofibrant_of_equiv (finite_is_cofibrant (Fin 0)) {
      toFun := Fin.elim0
      invFun := fun a => False.elim (hp a.property)
      left_inv := fun a => Fin.elim0 a
      right_inv := fun a => False.elim (hp a.property)
    }

end Tltt.Fibrancy
