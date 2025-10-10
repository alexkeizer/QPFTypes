import StateMachine.Basic
import Qpf


def StreamF : MvPFunctor 2 where
  A := Unit
  B _ := !![Fin 1, Fin 1]

@[match_pattern]
def StreamF.cons (x : α) (xs : ρ) : StreamF !![α, ρ] :=
  ⟨(), fun
    | 1, _ => x
    | 0, _ => xs
  ⟩

namespace StateStream

def Stream (α : Type) :=
  -- MvQPF.StateCofixShrunk StreamF !![α]
  MvQPF.Cofix StreamF !![α]

def Stream.nats : Stream Nat :=
  .corec (β := Nat) (fun i => StreamF.cons i (i+1)) 0

def Stream.head (s : Stream Nat) : Nat :=
  match MvQPF.repr s.dest with
  | ⟨(), f⟩ => f 1 (0 : Fin 1)

def Stream.tail (s : Stream Nat) : Stream Nat :=
  match MvQPF.repr s.dest with
  | ⟨(), f⟩ => f 0 (0 : Fin 1)

/-
The following is slightly unfortunate, it seems the Shrunk representation does
not admit `head_nats` as a def-eq. Note that `Cofix` does have this as a
def-eq!
-/
theorem head_nats : Stream.head (Stream.nats) = 0 := by
  native_decide
  -- ^^ This really ought to be true by `rfl`


def Stream.multiply (s : Stream Nat) (k : Nat) : Stream Nat :=
  let f s := StreamF.cons (s.head * k) s.tail
  .corec f s

end StateStream
open StateStream

def main : IO Unit := do
  let mut xs := (Stream.nats.multiply 2)
  let mut start ← IO.monoMsNow
  for _ in [0:50000] do
    let x := xs.head
    xs := xs.tail
    if x % 100 = 0 then
      let stop ← IO.monoMsNow
      IO.println s!"{x}\t\tElapsed: {stop - start}ms"
      start := stop
