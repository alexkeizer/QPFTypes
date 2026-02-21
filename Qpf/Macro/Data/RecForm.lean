import Qpf.Macro.Data.Replace

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term
open Lean.Parser.Tactic (inductionAlt)

/--
  The recursive form encodes how a function argument is recursive.
  Examples ty R α:
   α      → R α       → List (R α) → R α
  [nonRec,  directRec,  composed        ]
-/
inductive RecursionForm where
  | nonRec (stx : Term)
  | directRec
  | composed (stx : Term) -- Not supported yet
deriving Repr, BEq

namespace RecursionForm

variable {m} [Monad m] [MonadQuotation m]

private def containsStx (top : Term) (search : Term) : Bool :=
  (top.raw.find? (· == search)).isSome

partial def getArgTypes (v : Term) : List Term := match v.raw with
  | .node _ ``arrow #[arg, _, deeper] =>
     ⟨arg⟩ :: getArgTypes ⟨deeper⟩
  | rest => [⟨rest⟩]

partial def toType (retTy : Term) : List Term → m Term
  | [] => pure retTy
  | hd :: tl => do `($hd → $(← toType retTy tl))

/-- Extract takes a constructor and extracts its recursive forms.
This function assumes the pre-processor has run
It also assumes you don't have polymorphic recursive types such as
data Ql α | nil | l : α → Ql Bool → Ql α -/
def extract (view : CtorView) (rec_type : Term) : List RecursionForm := do
  if let some type := view.type? then
    let type_ls := (getArgTypes ⟨type⟩).dropLast

    type_ls.map fun v =>
      if v == rec_type then .directRec
      else if containsStx v rec_type then
          .composed v
      else .nonRec v
  else []

def extractWithName (topName : Name) (view : CtorView) (rec_type : Term) : Name × List RecursionForm :=
  (view.declName.replacePrefix topName .anonymous , extract view rec_type)

def replaceRec (old new : Term) : RecursionForm → Term
  | .nonRec x => x
  | .directRec => new
  | .composed x => ⟨Replace.replaceAllStx old new x⟩

def toTerm (recType : Term) : RecursionForm → Term
  | .nonRec x | .composed x => x
  | .directRec => recType

end RecursionForm
