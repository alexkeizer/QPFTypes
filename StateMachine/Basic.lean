import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Logic.Small.Defs

namespace MvQPF
open MvFunctor
open TypeVec

universe u v w

variable {n} (F : TypeVec.{u} (n + 1) → Type u) [MvQPF F]

/-- A pointed coalgebra -/
structure Coalg (α : TypeVec.{u} n) : Type (u+1) where
  corec ::
    {σ : Type u}
    (dest' : σ → F (α ::: σ))
    (s : σ)

/-- info: @Coalg.corec n F α : {σ : Type u} → (σ → F (α ::: σ)) → σ → Coalg F α -/
#guard_msgs (whitespace := lax) in
  variable {α} in
  #check (@Coalg.corec _ F α)

variable {F} {α : TypeVec.{u} n}

namespace Coalg
variable {self : Coalg F α}

/-! ## Basic API -/

/-!
NOTE: we'd like to define a `dest` function like so:
```
def dest (self : StateCofix F α) : F (α ::: (StateCofix F α)) := _
```
However, this doesn't type-check, because of the universe bump in `StateCofix`,
so we content ourselves with having the current `dest` projection, which returns
a state in the current coalgebra.
-/

def dest (self : Coalg F α) : F (α ::: self.σ) := self.dest' self.s

/-! ## Bisim -/

def IsBisim (R : self.σ → self.σ → Prop) : Prop :=
    ∀ s t, R s t →
      LiftR (RelLast _ R) (self.dest' s) (self.dest' t)

/-
The following definition using `coinductive_fixpoint` fails
-/

-- def BisimStates' (self : StateCofix F α) : self.σ → self.σ → Prop :=
--   fun s t =>
--     let R := RelLast _ (BisimStates' self)
--     LiftR R (self.dest' s) (self.dest' t)
--   coinductive_fixpoint
-- ^^ Fails to show monotonicity
--    TODO: ask wojciech


/--
Given two pointed coalgebras `c` and `d`, return the disjoint union coalgebra which
embeds both coalgebras, with `c` as the designated point, together with the state
of the union coalgebra which represents `d`.
-/
def union (c d : Coalg F α) : Coalg F α where
  σ := c.σ ⊕ d.σ
  s := .inl c.s
  dest' s := match s with
          | .inl s => MvFunctor.map (TypeVec.id ::: .inl) (c.dest' s)
          | .inr s => MvFunctor.map (TypeVec.id ::: .inr) (d.dest' s)


def Bisim : Coalg F α → Coalg F α → Prop := fun c d =>
  let un := c.union d
  ∃ R, IsBisim (self := un) R ∧ R (.inl c.s) (.inr d.s)

infixl:60 " ~ " => Bisim

section UnionLemmas

theorem union_dest_eq_left (c d : Coalg F α) (s : c.σ) :
    (TypeVec.id ::: Sum.inl) <$$> c.dest' s = (c.union d).dest' (.inl s) :=
  rfl

theorem union_dest_eq_right (c d : Coalg F α) (s : d.σ) :
    (TypeVec.id ::: Sum.inr) <$$> d.dest' s = (c.union d).dest' (.inr s) :=
  rfl

end UnionLemmas

/-!
## Conversions to/from default Cofix type
-/

def toCofix (self : Coalg F α) : Cofix F α :=
  Cofix.corec self.dest' self.s

def ofCofix (fix : Cofix F α) : Coalg F α :=
  corec Cofix.dest fix

@[simp]
theorem toCofix_ofCofix (fix : Cofix F α) : toCofix (ofCofix fix) = fix := by
  simp only [toCofix, ofCofix]
  apply MvQPF.Cofix.bisim (fun s t => s = Cofix.corec Cofix.dest t)
  · rintro _ x rfl
    rw [Cofix.dest_corec, MvQPF.liftR_iff]
    let r := repr x.dest
    use r.fst
    use ((TypeVec.id ::: Cofix.corec Cofix.dest) ⊚ r.snd)
    use r.snd
    simp only [r]
    and_intros
    · change _ = abs (_ <$$> repr _)
      simp [abs_repr, abs_map]
    · simp [abs_repr]
    · intro i j
      cases i
      <;> rfl
  · rfl

theorem ofCofix_toCofix (self : Coalg F α) : ofCofix (toCofix self) ~ self := by
  simp only [toCofix, ofCofix]
  simp only [Bisim, union]
  use fun
    | .inl s, .inr t => s = Cofix.corec self.dest' t
    | _,  _ => False
  apply And.intro ?_ rfl
  simp only [IsBisim, Sum.forall, IsEmpty.forall_iff, implies_true, true_and, and_true]
  rintro _ s rfl
  rw [Cofix.dest_corec, MvFunctor.map_map, ← TypeVec.appendFun_comp_id]
  rw [MvQPF.liftR_iff]
  let r := repr (self.dest' s)
  use r.fst
  use ((TypeVec.id ::: Sum.inl ∘ Cofix.corec self.dest') ⊚ r.snd)
  use ((TypeVec.id ::: Sum.inr) ⊚ r.snd)
  simp only [r]
  and_intros
  · change _ = abs (_ <$$> repr (self.dest' s))
    simp [abs_map, abs_repr]
  · change _ = abs (_ <$$> repr (self.dest' s))
    simp [abs_map, abs_repr]
  · intro i j
    cases i <;> rfl

end Coalg

variable (F) (α) in
def StateCofixFinal := Quot (Coalg.Bisim (F := F) (α := α))

namespace StateCofixFinal

/-!
## Basic API
-/

def corec {β} (f : β → F (α ::: β)) (init : β) : StateCofixFinal F α :=
  Quot.mk _ <| Coalg.corec f init

/-!
Now the big question is, how do we define `dest` for the final coalgebra here?
We can't refer to the state space, because that certainly wouldn't respect the
quotient, but we can't return a `StateCofixFinal` either, because of the universe
bump!

Hence, we need to shrink
-/

/-!
## Equivalence
-/

def toCofix (self : StateCofixFinal F α) : Cofix F α :=
  have h := by
    -- to show: two bisimilar coalgebras generate the same cofix
    -- This is true, and proving it shouldn't be too hard
    rintro a b ⟨R, h_bisim, h_R⟩
    let R' : Cofix F α → Cofix F α → Prop := fun x y =>
      ∃ (s : a.σ) (t : b.σ),
          R (.inl s) (.inr t)
          ∧ x = Coalg.toCofix { a with s := s }
          ∧ y = Coalg.toCofix { b with s := t }
    apply MvQPF.Cofix.bisim R'
    · simp only [forall_exists_index, and_imp, R']
      rintro _ _ s t hR rfl rfl
      sorry
    · exact ⟨_, _, h_R, rfl, rfl⟩
  Quot.lift Coalg.toCofix h self

def ofCofix (fix : Cofix F α) : StateCofixFinal F α :=
  Quot.mk _ <| .ofCofix fix

@[simp]
theorem toCofix_ofCofix (fix : Cofix F α) : toCofix (ofCofix fix) = fix := by
  simp [ofCofix, toCofix]

@[simp]
theorem ofCofix_toCofix (self : StateCofixFinal F α) : ofCofix (toCofix self) = self := by
  simp only [ofCofix, toCofix]
  cases self using Quot.induction_on
  apply Quot.sound
  simpa using Coalg.ofCofix_toCofix _

def equivCofix : StateCofixFinal F α ≃ Cofix F α where
  toFun := toCofix
  invFun := ofCofix
  left_inv := ofCofix_toCofix
  right_inv := toCofix_ofCofix

instance : Small.{u} (StateCofixFinal F α) where
  equiv_small := ⟨_, ⟨equivCofix⟩⟩

end StateCofixFinal

section CShrink
variable (α : Type v) [Small.{w} α]

noncomputable
opaque CShrinkDef : Σ (β : Type w), α ≃ β := ⟨Shrink α, equivShrink _⟩

def CShrink := (CShrinkDef α).1

variable {α}

unsafe def CShrink.ofLargeImpl : α → CShrink α := unsafeCast
@[implemented_by CShrink.ofLargeImpl]
abbrev CShrink.ofLarge : α → CShrink α := (CShrinkDef _).2

unsafe def CShrink.toLargeImpl : CShrink α → α := unsafeCast
@[implemented_by CShrink.toLargeImpl]
abbrev CShrink.toLarge : CShrink α → α := (CShrinkDef _).2.invFun

end CShrink

variable (F) (α) in
def StateCofixShrunk := CShrink (StateCofixFinal F α)

namespace StateCofixShrunk

/-!
## Basic API

Note this is noncomputable (for now!) because of the Shrink
-/
section

protected def ofLarge : StateCofixFinal F α → StateCofixShrunk F α :=
  CShrink.ofLarge
protected def toLarge : StateCofixShrunk F α → StateCofixFinal F α :=
  CShrink.toLarge
open StateCofixShrunk (ofLarge toLarge)

def corec {β} (f : β → F (α ::: β)) (init : β) : StateCofixShrunk F α :=
  .ofLarge <| .corec f init

def dest (self : StateCofixShrunk F α) : F (α ::: (StateCofixShrunk F α)) :=
  let f self := (TypeVec.id ::: corec self.dest') <$$> self.dest
  have h := by
    show ∀ a b, a ~ b → f a = f b
    -- ^^ Non-trivial to formalize, but clearly true
    rintro a b h_bisim
    unfold Coalg.Bisim at h_bisim
    rcases h_un : a.union b with ⟨un, d'⟩
    simp only [Coalg.dest, f]
    -- At this point, we should rewrite `a.dest' a.s` and `b.dest' b.s` into
    -- some phrasing in terms of `union`.
    unfold corec StateCofixFinal.corec
    sorry
  Quot.lift f h self.toLarge

/-!
## Equivalence

TODO: compose the existing equivalences to show the equivalence between `Cofix`
      and `StateCofixShrunk`.

TODO: we probably want to have some proof that relates the above `corec` to
      `Cofix.corec` and `dest` to `Cofix.dest`.
-/

end

end StateCofixShrunk

end MvQPF
