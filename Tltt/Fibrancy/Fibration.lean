import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.HasLimits
import Tltt.Fibrancy.FibrantLift

namespace Tltt.Fibrancy
open Hott
open CategoryTheory

def is_fibration_weak {α β : Type*} (f : α → β) : Type _ :=
  ∀ y : β, IsFibrantWeak { x : α // f x = y }

abbrev tot {α : Type*} (β : α → Typeₒ) : Σ γ : Type _, γ → α :=
  ⟨Σ a, β a, Sigma.fst⟩

def is_fibration_strict {α β : Type _} (f : α → β) : Type _ :=
  { x // tot x = ⟨α, f⟩ }

def fibration_stable_identity.{u} {α β γ δ : Type u} (p : α = β) (f : β → γ) (q : γ = δ)
                              (fib : is_fibration_strict f)
                              : is_fibration_strict (eqToHom q ∘ f ∘ eqToHom p) := by
  induction p
  induction q
  simp
  assumption

private def sigma_fiber_equiv.{u} {β : Type u} (B : β → Type u) (y : β) :
    {x : Σ b, B b // x.1 = y} ≃ B y where
  toFun x := x.2 ▸ x.1.2
  invFun b := ⟨⟨y, b⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b, x⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

@[instance_reducible]
def strict_fibration_fiber_fibrant.{u} {α β : Type u} (f : α → β)
    (fib : is_fibration_strict f) (y : β) : IsFibrantWeak {x : α // f x = y} := by
  rcases fib with ⟨B, h⟩
  have h' : IsFibrantWeak {x : (tot B).1 // (tot B).2 x = y} := by
    refine ⟨B y, (sigma_fiber_equiv (fun b => (B b : Type u)) y).symm⟩
  change IsFibrantWeak {x : (⟨α, f⟩ : Σ γ : Type u, γ → β).1 //
    (⟨α, f⟩ : Σ γ : Type u, γ → β).2 x = y}
  rw [← h]
  exact h'

end Tltt.Fibrancy
