import Tltt.ObjLang
import Tltt.Tactics

open Tltt.Hott

noncomputable section
namespace TlttTests

universe u v

-- Recursive constructors and recursors must keep their kernel computation rules.
inductiveₒ Natₒ : Typeₒ where
  | zero : Natₒ
  | succ (n : Natₒ) : Natₒ

def add (n m : Natₒ) : Natₒ :=
  Natₒ.recₒ n (fun _ ih => Natₒ.succ ih) m

example (n : Natₒ) : add n Natₒ.zero = n := rfl
example (n m : Natₒ) : add n (Natₒ.succ m) = Natₒ.succ (add n m) := rfl

-- Parameters remain implicit in the generated recursor.
inductiveₒ Listₒ (α : Typeₒ) : Typeₒ where
  | nil : Listₒ α
  | cons (head : α) (tail : Listₒ α) : Listₒ α

def length {α : Typeₒ} : Listₒ α → Natₒ :=
  Listₒ.recₒ Natₒ.zero (fun _ _ ih => Natₒ.succ ih)

example {α : Typeₒ} : length (Listₒ.nil (α := α)) = Natₒ.zero := rfl
example {α : Typeₒ} (a : α) (xs : Listₒ α) :
    length (Listₒ.cons a xs) = Natₒ.succ (length xs) := rfl

-- Constructor indices are analyzed inside the object-type lifting wrapper.
inductiveₒ Vecₒ (α : Typeₒ) : Natₒ → Typeₒ where
  | nil : Vecₒ α Natₒ.zero
  | cons (n : Natₒ) (head : α) (tail : Vecₒ α n) : Vecₒ α (Natₒ.succ n)

def count {α : Typeₒ} {n : Natₒ} (xs : Vecₒ α n) : Natₒ :=
  Vecₒ.recₒ (motive := fun _ _ => Natₒ) Natₒ.zero
    (fun _ _ _ ih => Natₒ.succ ih) n xs

example {α : Typeₒ} : count (Vecₒ.nil (α := α)) = Natₒ.zero := rfl
example {α : Typeₒ} (n : Natₒ) (a : α) (xs : Vecₒ α n) :
    count (Vecₒ.cons n a xs) = Natₒ.succ (count xs) := rfl

inductiveₒ Liftₒ (α : Typeₒ u) : Typeₒ max u v where
  | up (down : α) : Liftₒ α

example {α : Typeₒ u} (a : α) :
    Liftₒ.recₒ (motive := fun _ : Liftₒ.{u, v} α => α) id (Liftₒ.up a) = a := rfl

-- Recursion through a function supplies a pointwise induction hypothesis.
inductiveₒ Treeₒ : Typeₒ where
  | leaf : Treeₒ
  | node (children : Natₒ → Treeₒ) : Treeₒ

def firstBranchLength : Treeₒ → Natₒ :=
  Treeₒ.recₒ Natₒ.zero (fun _ ih => Natₒ.succ (ih Natₒ.zero))

example (children : Natₒ → Treeₒ) :
    firstBranchLength (Treeₒ.node children) =
      Natₒ.succ (firstBranchLength (children Natₒ.zero)) := rfl

-- Object paths inhabit their own type; their computation is stated with strict equality.
example {α : Typeₒ} (x : α) : x =ₒ x := Id.refl x
example {α : Typeₒ} (x : α) :
    Id.elim (P := fun _ _ _ => α) id x x (Id.refl x) = x := rfl
example {α : Typeₒ} {β : α → Typeₒ} (f : (x : α) → β x) (x : α) :
    Pi.app (Pi.lam f) x = f x := rfl

example {α : Typeₒ} (x y : α) (p : x =ₒ y) : True := by
  fail_if_success have : x = y := p
  trivial

-- The named path-induction form must leave `refl` available as an identifier.
namespace PathInduction

def refl {α : Typeₒ} (x : α) : x =ₒ x := Id.refl x

example {α : Typeₒ} (x : α) : x =ₒ x := refl x

example {α : Typeₒ} (x y : α) (p : x =ₒ y) : y =ₒ x := by
  path_inductionₒ p with refl z
  exact refl z

example {α : Typeₒ} (x y : α) (p : x =ₒ y) : y =ₒ x := by
  path_inductionₒ p
  rflₒ

end PathInduction

run_cmd do
  for recursor in [``Natₒ.recₒ, ``Listₒ.recₒ, ``Vecₒ.recₒ, ``Liftₒ.recₒ, ``Treeₒ.recₒ] do
    let axioms ← Lean.collectAxioms recursor
    unless axioms.isEmpty do
      throwError "Generated recursor {recursor} depends on axioms: {axioms}"

end TlttTests
