import Tltt.Hott
import Tltt.DirectCategories
import Tltt.Fibrancy
import Finite
import Tltt.Reedy
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- The ordinal category uses conversion through its semireducible Nat wrapper.
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Tltt
open Hott
open Fibrancy
open ReedyFibrancy

def SemiSimplexCat :=
  Nat

instance : DecidableEq SemiSimplexCat := inferInstanceAs <| DecidableEq Nat

namespace SemiSimplexCat
  def Hom (n : SemiSimplexCat) (m : SemiSimplexCat) :=
    { f : Fin n → Fin m // ∀ x y, x < y → f x < f y }

  protected def id (a : SemiSimplexCat) : Hom a a where
    val := id
    property := by
      intro x y h
      assumption

  protected def comp {a b c : SemiSimplexCat} (f : Hom a b) (g : Hom b c) : Hom a c where
    val := g.val ∘ f.val
    property := by
      intro x y  h
      apply g.property
      apply f.property
      assumption

  instance : Category SemiSimplexCat where
    Hom := SemiSimplexCat.Hom
    id := SemiSimplexCat.id
    comp := SemiSimplexCat.comp

  abbrev nat_cat := Preorder.smallCategory Nat

  def rank.obj (n : SemiSimplexCat) : Nat := n

  @[simp]
  theorem obj.beta (n : SemiSimplexCat) : rank.obj n = n := by
    rfl
  
  def rank.map : ∀ {n m : SemiSimplexCat}, Hom n m → nat_cat.Hom n m := by
    intro (n : Nat) (m : Nat) f
    apply ULift.up
    apply PLift.up
    let ⟨f, f_inc⟩ := f
    have : ∀ i : Fin n, (f i).val ≥ i.val := by
      intro i
      let rec l : (i : Nat) → (p : i < n) → (f ⟨i, p⟩).val ≥ i
      | 0, _ => by simp
      | i+1, p => by
        have i_lt_n : i < n := by
          apply Nat.lt_of_succ_lt
          assumption
        simp +arith +decide
        calc i
          _ ≤ f ⟨i, i_lt_n⟩ := l i i_lt_n
          _ < f ⟨i+1, _⟩ := by
            apply f_inc
            simp +arith +decide
      apply l
    match n with
    | 0 => simp
    | n+1 =>
      have := this (Fin.last n)
      simp at this
      calc n + 1
        _ ≤ f (Fin.last n) + 1 := by simp +arith +decide; exact this
        _ ≤ m := by
          apply Nat.succ_le_of_lt
          apply Fin.isLt

  theorem rank.map_id : ∀ n : SemiSimplexCat, map (𝟙 n) = 𝟙 (obj n) := by
    intro (n : Nat)
    rfl

  theorem rank.map_comp : ∀ {m n l : SemiSimplexCat} (f : Hom m n) (g : Hom n l),
                      map (SemiSimplexCat.comp f g) = map f ≫ map g := by
    intro (m : Nat) (n : Nat) (l : Nat) f g
    rfl

  def rank : @Functor SemiSimplexCat _ Nat nat_cat where
    obj := rank.obj
    map := rank.map
    map_id := rank.map_id
    map_comp := rank.map_comp

  instance : DirectCategory SemiSimplexCat where
    rank := SemiSimplexCat.rank
    reflect_identity := by
      intro (n : Nat) (m : Nat) f p
      have p : n = m := p
      revert f
      rewrite [p]
      intro ⟨f, q⟩
      congr
      funext a
      simp
      have p₁ (a b : Nat) (a_lt_m : a < m) (ab_lt_m : a + b < m)
              : f ⟨a, a_lt_m⟩ + b ≤ f ⟨a + b, ab_lt_m⟩ := by
        let a' : Fin m := ⟨a, a_lt_m⟩
        induction b with
        | zero => simp
        | succ b ih =>
          simp only [Nat.add_succ, Nat.succ_le_iff]
          have ab_lt_m' : a+b < m := by
            apply Nat.le_of_succ_le
            exact ab_lt_m
          calc f a' + b
            _ ≤ f ⟨a + b, ab_lt_m'⟩ := by apply ih
            _ < f ⟨a + b + 1, ab_lt_m⟩ := by
              apply q
              simp +arith +decide
      have p₂ (a : Fin m) : a ≤ f a := by
        cases m
        case zero =>
          exfalso
          apply Nat.not_lt_zero
          exact a.isLt
        case succ m _ _ =>
          calc ↑a
            _ ≤ (f ⟨0, Nat.zero_lt_succ m⟩).val + a := by apply Nat.le_add_left a
            _ ≤ f ⟨0+a.val, by simpa using a.isLt⟩ := by apply p₁ 0 a (Nat.zero_lt_succ m)
            _ = f a := by simp
      have p₃ : a.val ≤ f a := p₂ a
      if h : a.val < f a then
        exfalso
        cases m
        case zero =>
          apply Nat.not_lt_zero
          apply a.isLt
        case succ m _ =>
          let b := m - a
          have a_b_eq_m : ↑a + b = m := by
            have : ↑a ≤ m := by
              apply Nat.le_of_lt_succ
              exact a.isLt
            rw [← Nat.add_sub_assoc this a]
            simp
          apply Nat.lt_irrefl (m+1)
          calc m+1
            _ = (↑a + b) + 1 := by rw [a_b_eq_m]
            _ ≤ f a + b := by
              apply Nat.add_lt_add_right
              assumption
            _ ≤ f ⟨a + b, by rw [a_b_eq_m]; simp⟩ := by
              apply p₁ a b a.isLt
            _ < m+1 := by
              apply Fin.isLt (f ⟨a + b, by rw [a_b_eq_m]; simp⟩)
      else
        apply Fin.eq_of_val_eq
        apply Nat.le_antisymm
        · apply Nat.le_of_not_gt
          exact h
        · apply p₂

  def finite_rank (n : Nat) : Finite (OfRank SemiSimplexCat n) where
    card := 1
    equiv := {
      toFun := fun _ => 0
      invFun := fun _ => ⟨n, rfl⟩
      left_inv := by
        intro ⟨a, a_eq_n⟩
        simp
        rw [← a_eq_n]
        rfl
      right_inv := by
        intro b
        exact Subsingleton.elim _ b
    }
  @[instance_reducible]
  def finite_hom (n m : SemiSimplexCat) : Finite (n ⟶ m) := by
    classical
    letI : Fintype (n ⟶ m) :=
      inferInstanceAs (Fintype { f : Fin n → Fin m // ∀ x y, x < y → f x < f y })
    exact Finite.of_fintype _
end SemiSimplexCat

section
universe u v

/-- Cofibrant ranks and incoming hom types make matching objects fibrant.
The extension families use cofibrancy of each rank one universe higher, at the
universe of inner type codes. -/
@[instance_reducible]
def cofibrant_reedy_presheaf_is_fibrant (D : Type u)
    [DirectCategory.{u, max u v} D] (n : Nat)
    (cofibrant_ranks : ∀ k, IsCofibrant.{u, max u v, max u v} (OfRank D k))
    (cofibrant_code_ranks : ∀ k,
      IsCofibrant.{u, (max u v)+1, (max u v)+1} (OfRank D k))
    (cofibrant_homs : ∀ i j : D,
      IsCofibrant.{max u v, max u v, max u v} (i ⟶ j)) :
    IsFibrantWeak.{(max u v)+1, (max u v)+1} (ReedyPresheaf D n) := by
  induction n with
  | zero =>
    apply fib_below_zero
  | succ n ih =>
    apply fibrant_of_eqv_fibrant (α := SigmaCompactLRP D n)
    · apply sigma_fibrant.{(max u v)+1, (max u v)+1, (max u v)+1, (max u v)+1}
      · assumption
      · intro X
        apply (cofibrant_code_ranks n).pi_fibrant
        intro x
        apply pi_fibrant.{max u v, (max u v)+1, max u v, (max u v)+1}
        · induction x with | mk x rk_x_eq_n =>
          induction rk_x_eq_n
          exact matching_object_fibrant x X cofibrant_ranks (fun j => cofibrant_homs j x)
        · intro
          apply fibrant_weakening
          apply lift_is_fibrant
    · apply Equiv.symm
      apply rdpsh_eqv_compact

/-- Finite ranks and hom types supply cofibrancy at both required universes. -/
def finite_reedy_presheaf_is_fibrant (D : Type u)
    [DirectCategory.{u, max u v} D] [DecidableEq D] (n : Nat)
    (finite_ranks : ∀ k, Finite (OfRank D k))
    (finite_homs : ∀ i j : D, Finite (i ⟶ j)) :
    IsFibrantWeak.{(max u v)+1, (max u v)+1} (ReedyPresheaf D n) := by
  apply cofibrant_reedy_presheaf_is_fibrant D n
  · intro k
    letI := finite_ranks k
    exact finite_is_cofibrant _
  · intro k
    letI := finite_ranks k
    exact finite_is_cofibrant _
  · intro i j
    letI := finite_homs i j
    exact finite_is_cofibrant _

end

def SemiSimplicialType (n : ℕ) : Typeₒ :=
  finite_reedy_presheaf_is_fibrant SemiSimplexCat n
    SemiSimplexCat.finite_rank SemiSimplexCat.finite_hom |>.obj_type

end Tltt
end
